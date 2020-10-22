// Copyright 2020 The JSpecify Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package com.google.jspecify.nullness;

import static com.sun.source.tree.Tree.Kind.NULL_LITERAL;
import static java.util.Arrays.asList;
import static java.util.Collections.emptyList;
import static java.util.Collections.unmodifiableList;
import static javax.lang.model.element.ElementKind.ENUM_CONSTANT;
import static javax.lang.model.element.ElementKind.PACKAGE;
import static javax.lang.model.type.TypeKind.ARRAY;
import static javax.lang.model.type.TypeKind.DECLARED;
import static javax.lang.model.type.TypeKind.INTERSECTION;
import static javax.lang.model.type.TypeKind.NULL;
import static javax.lang.model.type.TypeKind.WILDCARD;
import static org.checkerframework.framework.qual.TypeUseLocation.OTHERWISE;
import static org.checkerframework.framework.qual.TypeUseLocation.UNBOUNDED_WILDCARD_UPPER_BOUND;
import static org.checkerframework.javacutil.AnnotationUtils.areSame;
import static org.checkerframework.javacutil.TreeUtils.elementFromUse;
import static org.checkerframework.javacutil.TypesUtils.wildcardToTypeParam;

import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.Tree;
import com.sun.tools.javac.code.Type.WildcardType;
import java.lang.annotation.Annotation;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.TypeParameterElement;
import javax.lang.model.type.TypeMirror;
import javax.lang.model.util.Elements;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeFormatter;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedDeclaredType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedPrimitiveType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedTypeVariable;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedWildcardType;
import org.checkerframework.framework.type.DefaultAnnotatedTypeFormatter;
import org.checkerframework.framework.type.DefaultTypeHierarchy;
import org.checkerframework.framework.type.ElementQualifierHierarchy;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.StructuralEqualityComparer;
import org.checkerframework.framework.type.StructuralEqualityVisitHistory;
import org.checkerframework.framework.type.TypeHierarchy;
import org.checkerframework.framework.type.TypeVariableSubstitutor;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.type.typeannotator.TypeAnnotator;
import org.checkerframework.framework.util.AnnotationFormatter;
import org.checkerframework.framework.util.DefaultAnnotationFormatter;
import org.checkerframework.framework.util.defaults.QualifierDefaults;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.jspecify.annotations.DefaultNonNull;

public final class NullSpecAnnotatedTypeFactory
        extends GenericAnnotatedTypeFactory<CFValue, CFStore, CFTransfer, CFAnalysis> {
    private final AnnotationMirror noAdditionalNullness;
    private final AnnotationMirror unionNull;
    private final AnnotationMirror codeNotNullnessAware;

    private final boolean leastConvenientWorld;

    public NullSpecAnnotatedTypeFactory(BaseTypeChecker checker) {
        // Only use flow-sensitive type refinement if implementation code should be checked
        super(checker, checker.hasOption("checkImpl"));

        /*
         * The names here ("codeNotNullnessAware", etc.) are less ambiguous than the annotation
         * names ("NullnessUnspecified," etc.): If a type has nullness codeNotNullnessAware, that
         * doesn't necessarily mean that it has the @NullnessUnspecified annotation written on it in
         * source code. The other possibility is that it gets that value from the default in effect.
         *
         * Still, for the annotations that are actually printed in error messages (that is, the ones
         * without @InvisibleQualifier), we want the user-facing class names to match what users at
         * least *could* write in source code. So we use the less ambiguous names for our fields
         * here while still using the user-facing names for most of the classes.
         *
         * (An alternative would be to write a custom AnnotationFormatter to replace the names, but
         * that sounds like more trouble than it's worth.)
         */
        noAdditionalNullness = AnnotationBuilder.fromClass(elements, NoAdditionalNullness.class);
        unionNull = AnnotationBuilder.fromClass(elements, Nullable.class);
        codeNotNullnessAware = AnnotationBuilder.fromClass(elements, NullnessUnspecified.class);

        addAliasedAnnotation(org.jspecify.annotations.Nullable.class, unionNull);
        addAliasedAnnotation(
                org.jspecify.annotations.NullnessUnspecified.class, codeNotNullnessAware);

        if (checker.hasOption("aliasCFannos")) {
            addAliasedAnnotation(
                    org.checkerframework.checker.nullness.qual.Nullable.class, unionNull);
        }

        leastConvenientWorld = checker.hasOption("strict");

        postInit();
    }

    @Override
    protected Set<Class<? extends Annotation>> createSupportedTypeQualifiers() {
        return new LinkedHashSet<>(
                asList(Nullable.class, NullnessUnspecified.class, NoAdditionalNullness.class));
    }

    @Override
    protected QualifierHierarchy createQualifierHierarchy() {
        return new NullSpecQualifierHierarchy(getSupportedTypeQualifiers(), elements);
    }

    private final class NullSpecQualifierHierarchy extends ElementQualifierHierarchy {
        NullSpecQualifierHierarchy(
                Collection<Class<? extends Annotation>> qualifierClasses, Elements elements) {
            super(qualifierClasses, elements);
        }

        @Override
        public boolean isSubtype(AnnotationMirror subAnno, AnnotationMirror superAnno) {
            /*
             * Since we perform all necessary checking in the isSubtype method in
             * NullSpecTypeHierarchy, I tried replacing this body with `return true` to avoid
             * duplicating logic. However, that's a problem because the result of this method is
             * sometimes cached and used instead of a full call to the isSubtype method in
             * NullSpecTypeHierarchy.
             *
             * Specifically: DefaultTypeHierarchy.visitDeclared_Declared calls isPrimarySubtype,
             * which calls isAnnoSubtype, which directly calls NullSpecQualifierHierarchy.isSubtype
             * (as opposed to NullSpecTypeHierarchy.isSubtype). That's still fine, since we'll
             * reject the types in NullSpecTypeHierarchy.isSubtype. The problem, though, is that it
             * also inserts a cache entry for the supposed subtyping relationship, and that entry
             * can cause future checks to short-circuit. (I think I saw this in isContainedBy.)
             */
            boolean subIsUnspecified = areSame(subAnno, codeNotNullnessAware);
            boolean superIsUnspecified = areSame(superAnno, codeNotNullnessAware);
            boolean eitherIsUnspecified = subIsUnspecified || superIsUnspecified;
            boolean bothAreUnspecified = subIsUnspecified && superIsUnspecified;
            if (leastConvenientWorld && bothAreUnspecified) {
                return false;
            }
            if (!leastConvenientWorld && eitherIsUnspecified) {
                return true;
            }
            return areSame(subAnno, noAdditionalNullness) || areSame(superAnno, unionNull);
            /*
             * TODO(cpovirk): Consider overriding createQualifierKindHierarchy and overriding
             * DefaultQualifierKindHierarchy.createDirectSuperMap. Then see if I can remove my
             * @SubtypeOf annotations. (The @SubtypeOf annotations work fine as far as I can tell,
             * but they paint an incomplete picture.)
             *
             * TODO(cpovirk): Give our package-private annotations source retention (if that
             * actually prevents CF from writing them to bytecode)? (We don't want anyone to depend
             * on the presence of those particular annotations, since they're an implementation
             * detail of this checker. And it would of course be very easy for this CF checker
             * itself to come to depend on such annotations, since it will recognize them by
             * default!) Or maybe just edit CF to prevent them from being written to the bytecode
             * regardless of their retention?
             *
             * TODO(cpovirk): And/or eliminate our package-private annotations entirely in favor of
             * using the standard JSpecify annotations directly? Theoretically it's fine for *those*
             * to be written to bytecode. Still, it's a little sad that CF would be producing
             * different bytecode than other compilers. Then tools (including CF itself) might
             * behave differently depending on how a library was compiled.
             *
             * A tricky issue in all this may be NoAdditionalNullness: By default, CF requires
             * *some* annotation on all types (aside from type-variable usages). But currently,
             * JSpecify offers no annotation equivalent to NoAdditionalNullness. Fortunately, CF's
             * requirement for an annotation on all types is overrideable.
             *
             * Then there's another concern if we don't write NoAdditionalNullness and Nullable to
             * bytecode: When CF encounters a wildcard with implicit bounds, will it still write
             * those bounds explicitly to bytecode? If so, those bounds would likely be "missing"
             * annotations. For example:
             *
             * - For a `? super Foo` wildcard, CF may write `extends [...] Object`, as well. If it
             * does, we want it to write `@Nullable` -- and it should be the JSpecify @Nullable, not
             * our internal copy.
             *
             * - For a `? extends Foo` wildcard, CF may write `super [...] null`, as well?? (Or not?
             * Is that even expressible in bytecode?) If so, it sounds OK for there to be no
             * annotation there: The result should be treated as `super @NoAdditionalNullness null`,
             * which is correct. However, if the wildcard appeared in code that is *not* null-aware,
             * then the result would be treated as `super @NullnessUnspecified null`, which is
             * incorrect.
             *
             * This all needs research.
             */
        }

        @Override
        public AnnotationMirror leastUpperBound(
                AnnotationMirror qualifier1, AnnotationMirror qualifier2) {
            if (!areSame(getTopAnnotation(qualifier1), unionNull)
                    || !areSame(getTopAnnotation(qualifier2), unionNull)) {
                return null;
            }
            if (areSame(qualifier1, unionNull) || areSame(qualifier2, unionNull)) {
                return unionNull;
            }
            if (areSame(qualifier1, codeNotNullnessAware)
                    || areSame(qualifier2, codeNotNullnessAware)) {
                return codeNotNullnessAware;
            }
            return noAdditionalNullness;
        }

        @Override
        public AnnotationMirror greatestLowerBound(
                AnnotationMirror qualifier1, AnnotationMirror qualifier2) {
            if (!areSame(getTopAnnotation(qualifier1), unionNull)
                    || !areSame(getTopAnnotation(qualifier2), unionNull)) {
                return null;
            }
            if (areSame(qualifier1, noAdditionalNullness)
                    || areSame(qualifier2, noAdditionalNullness)) {
                return noAdditionalNullness;
            }
            if (areSame(qualifier1, codeNotNullnessAware)
                    || areSame(qualifier2, codeNotNullnessAware)) {
                return codeNotNullnessAware;
            }
            return unionNull;
        }
    }

    @Override
    protected TypeHierarchy createTypeHierarchy() {
        return new NullSpecTypeHierarchy(
                checker,
                getQualifierHierarchy(),
                checker.getBooleanOption("ignoreRawTypeArguments", true),
                checker.hasOption("invariantArrays"));
    }

    private final class NullSpecTypeHierarchy extends DefaultTypeHierarchy {
        NullSpecTypeHierarchy(
                BaseTypeChecker checker,
                QualifierHierarchy qualifierHierarchy,
                boolean ignoreRawTypeArguments,
                boolean invariantArrays) {
            super(checker, qualifierHierarchy, ignoreRawTypeArguments, invariantArrays);
        }

        @Override
        protected StructuralEqualityComparer createEqualityComparer() {
            return new NullSpecEqualityComparer(typeargVisitHistory);
        }

        @Override
        protected boolean visitTypevarSubtype(
                AnnotatedTypeVariable subtype, AnnotatedTypeMirror supertype) {
            /*
             * The superclass "projects" type-variable usages rather than unioning them.
             * Consequently, if we delegate directly to the supermethod, it can fail when it
             * shouldn't.  Fortunately, we already handle the top-level nullness subtyping in
             * isNullnessSubtype. So all we need to do here is to handle any type arguments. To do
             * that, we still delegate to the supertype. But first we mark the supertype as
             * unionNull so that the supertype's top-level check will always succeed.
             *
             * TODO(cpovirk): There are probably many more cases that we could short-circuit. We
             * might consider doing that in isSubtype rather than with overrides.
             */
            return super.visitTypevarSubtype(subtype, withUnionNull(supertype));
        }

        @Override
        protected boolean visitWildcardSubtype(
                AnnotatedWildcardType subtype, AnnotatedTypeMirror supertype) {
            // See discussion in visitTypevarSubtype above.
            return super.visitWildcardSubtype(subtype, withUnionNull(supertype));
        }

        @Override
        protected boolean visitTypevarSupertype(
                AnnotatedTypeMirror subtype, AnnotatedTypeVariable supertype) {
            /*
             * TODO(cpovirk): Why are the supertype cases so different from the subtype cases above?
             * In particular: Why is it important to replace an argument only conditionally? And why
             * is it important to replace the subtype instead of the supertype?
             */
            return super.visitTypevarSupertype(
                    isNullInclusiveUnderEveryParameterization(supertype)
                            ? withNoAdditionalNullness(subtype)
                            : subtype,
                    supertype);
        }

        @Override
        protected boolean visitWildcardSupertype(
                AnnotatedTypeMirror subtype, AnnotatedWildcardType supertype) {
            // See discussion in visitTypevarSupertype above.
            return super.visitWildcardSupertype(
                    isNullInclusiveUnderEveryParameterization(supertype)
                            ? withNoAdditionalNullness(subtype)
                            : subtype,
                    supertype);
        }

        @Override
        protected boolean isSubtype(
                AnnotatedTypeMirror subtype, AnnotatedTypeMirror supertype, AnnotationMirror top) {
            return super.isSubtype(subtype, supertype, top)
                    && isNullnessSubtype(subtype, supertype);
        }

        private boolean isNullnessSubtype(
                AnnotatedTypeMirror subtype, AnnotatedTypeMirror supertype) {
            if (subtype.getKind() == NULL && subtype.hasAnnotation(noAdditionalNullness)) {
                // Arises with the *lower* bound of type parameters and wildcards.
                return true;
            }
            if (supertype.getKind() == WILDCARD) {
                /*
                 * super.isSubtype already called back into this.isSameType (and thus into
                 * isNullnessSubtype) for the bound. That's fortunate, as we don't define
                 * subtyping rules for wildcards (since the JLS says that they should be capture
                 * converted by this point, or we should be checking their *bounds* for a
                 * containment check).
                 */
                return true;
            }
            return isNullInclusiveUnderEveryParameterization(supertype)
                    || isNullExclusiveUnderEveryParameterization(subtype)
                    || nullnessEstablishingPathExists(subtype, supertype);
        }
    }

    private boolean isNullInclusiveUnderEveryParameterization(AnnotatedTypeMirror type) {
        /*
         * We implement no special case for intersection types because it's not clear that
         * CF produces them in positions that could be the "supertype" side of a subtyping
         * check. That's primarily because it (mostly?) doesn't do capture conversion.
         */
        if (type.getKind() == INTERSECTION) {
            throw new RuntimeException("Unexpected intersection type: " + type);
        }
        /*
         * TODO(cpovirk): Do we need to explicitly handle aliases here (and elsewhere, including
         * in NullSpecVisitor, especially for DefaultNonNull)?
         */
        return type.hasAnnotation(unionNull)
                || (!leastConvenientWorld && type.hasAnnotation(codeNotNullnessAware));
    }

    boolean isNullExclusiveUnderEveryParameterization(AnnotatedTypeMirror subtype) {
        return nullnessEstablishingPathExists(
                subtype, t -> t.getKind() == DECLARED || t.getKind() == ARRAY);
    }

    private boolean nullnessEstablishingPathExists(
            AnnotatedTypeMirror subtype, AnnotatedTypeMirror supertype) {
        /*
         * TODO(cpovirk): As an optimization, `return false` if `supertype` is not a type
         * variable: If it's not a type variable, then the only ways for isNullnessSubtype to
         * succeed were already checked by isNullInclusiveUnderEveryParameterization and
         * isNullExclusiveUnderEveryParameterization.
         */
        return nullnessEstablishingPathExists(
                subtype, t -> checker.getTypeUtils().isSameType(t, supertype.getUnderlyingType()));
    }

    private boolean nullnessEstablishingPathExists(
            AnnotatedTypeMirror subtype, Predicate<TypeMirror> supertypeMatcher) {
        if (isUnionNullOrEquivalent(subtype)) {
            return false;
        }
        if (supertypeMatcher.test(subtype.getUnderlyingType())) {
            return true;
        }
        for (AnnotatedTypeMirror supertype : getUpperBounds(subtype)) {
            if (nullnessEstablishingPathExists(supertype, supertypeMatcher)) {
                return true;
            }
        }
        /*
         * We don't need to handle the "lower-bound rule" here: The Checker Framework doesn't
         * perform wildcard capture conversion. (Hmm, but it might see post-capture-conversion
         * types in some cases....) It compares "? super Foo" against "Bar" by more directly
         * comparing Foo and Bar.
         */
        return false;
    }

    private List<? extends AnnotatedTypeMirror> getUpperBounds(AnnotatedTypeMirror type) {
        switch (type.getKind()) {
            case INTERSECTION:
            case TYPEVAR:
                return withNoAdditionalNullness(type).directSuperTypes();

            case WILDCARD:
                List<AnnotatedTypeMirror> bounds = new ArrayList<>();

                bounds.addAll(withNoAdditionalNullness(type).directSuperTypes());

                /*
                 * We would use `((AnnotatedWildcardType) type).getTypeVariable()`, but it is not
                 * available in all cases that we need.
                 */
                WildcardType wildcard =
                        (WildcardType) type.getUnderlyingType(); // javac internal type
                TypeParameterElement typeParameter = wildcardToTypeParam(wildcard);
                if (typeParameter != null) {
                    bounds.add(getAnnotatedType(typeParameter));
                }

                return unmodifiableList(bounds);

            default:
                return emptyList();
        }
    }

    private boolean isUnionNullOrEquivalent(AnnotatedTypeMirror type) {
        return type.hasAnnotation(unionNull)
                || (leastConvenientWorld && type.hasAnnotation(codeNotNullnessAware));
    }

    private final class NullSpecEqualityComparer extends StructuralEqualityComparer {
        NullSpecEqualityComparer(StructuralEqualityVisitHistory typeargVisitHistory) {
            super(typeargVisitHistory);
        }

        @Override
        protected boolean checkOrAreEqual(AnnotatedTypeMirror type1, AnnotatedTypeMirror type2) {
            Boolean pastResult = visitHistory.result(type1, type2, /*hierarchy=*/ unionNull);
            if (pastResult != null) {
                return pastResult;
            }

            boolean result = areEqual(type1, type2);
            this.visitHistory.add(type1, type2, /*hierarchy=*/ unionNull, result);
            return result;
        }

        @Override
        public boolean areEqualInHierarchy(
                AnnotatedTypeMirror type1, AnnotatedTypeMirror type2, AnnotationMirror top) {
            return areEqual(type1, type2);
        }

        private boolean areEqual(AnnotatedTypeMirror type1, AnnotatedTypeMirror type2) {
            /*
             * I'd like to use the spec definition here: "type1 is a subtype of type2 and vice
             * versa." However, that produces infinite recursion in some cases.
             */
            boolean type1IsUnspecified = type1.hasAnnotation(codeNotNullnessAware);
            boolean type2IsUnspecified = type2.hasAnnotation(codeNotNullnessAware);
            boolean bothAreUnspecified = type1IsUnspecified && type2IsUnspecified;
            boolean eitherIsUnspecified = type1IsUnspecified || type2IsUnspecified;
            if (leastConvenientWorld && bothAreUnspecified) {
                return false;
            }
            if (!leastConvenientWorld && eitherIsUnspecified) {
                return true;
            }
            AnnotationMirror a1 = type1.getAnnotationInHierarchy(unionNull);
            AnnotationMirror a2 = type2.getAnnotationInHierarchy(unionNull);
            return a1 == a2 || (a1 != null && a2 != null && areSame(a1, a2));
            /*
             * TODO(cpovirk): Do we care about the base type, or is looking at annotations
             * enough? super.visitDeclared_Declared has a TODO with a similar question.
             * Err, presumably normal Java type-checking has done that job. A more interesting
             * question may be why we don't look at type args. The answer might be simply:
             * "That's the contract, even though it is surprising, given the names of the class
             * and its methods." (Granted, the docs of super.visitDeclared_Declared also say
             * that it checks that "The types are of the same class/interfaces," so the contract
             * isn't completely clear.)
             */
        }
    }

    @Override
    protected TypeVariableSubstitutor createTypeVariableSubstitutor() {
        return new NullSpecTypeVariableSubstitutor();
    }

    private final class NullSpecTypeVariableSubstitutor extends TypeVariableSubstitutor {
        @Override
        protected AnnotatedTypeMirror substituteTypeVariable(
                AnnotatedTypeMirror argument, AnnotatedTypeVariable use) {
            // TODO(cpovirk): Delegate to leastUpperBound?
            AnnotatedTypeMirror substitute = argument.deepCopy(/*copyAnnotations=*/ true);
            if (argument.hasAnnotation(unionNull) || use.hasAnnotation(unionNull)) {
                substitute.replaceAnnotation(unionNull);
            } else if (argument.hasAnnotation(codeNotNullnessAware)
                    || use.hasAnnotation(codeNotNullnessAware)) {
                substitute.replaceAnnotation(codeNotNullnessAware);
            }

            return substitute;
        }
    }

    @Override
    public AnnotatedDeclaredType getSelfType(Tree tree) {
        AnnotatedDeclaredType superResult = super.getSelfType(tree);
        return superResult == null ? null : withNoAdditionalNullness(superResult);
    }

    @Override
    protected QualifierDefaults createQualifierDefaults() {
        return new NullSpecQualifierDefaults(elements, this);
    }

    private final class NullSpecQualifierDefaults extends QualifierDefaults {
        NullSpecQualifierDefaults(Elements elements, AnnotatedTypeFactory atypeFactory) {
            super(elements, atypeFactory);
        }

        @Override
        public void annotate(Element elt, AnnotatedTypeMirror type) {
            if (elt == null) {
                super.annotate(elt, type);
                return;
            }

            /*
             * CF has some built-in support for package-level defaults. However, it is primarily
             * intended to support @DefaultQualifier (and it can't easily be extended to recognize
             * @DefaultNonNull).
             *
             * If we really wanted to, we could explicit set defaults for a package here, when
             * scanning a class in that package (addElementDefault(elt.getEnclosingElement(), ...)).
             * But the code is simpler if we just read the package default and set it as the default
             * for the class.
             *
             * XXX: When adding support for DefaultNullnessUnspecified, be sure that DefaultNullnessUnspecified on a *class*
             * overrides DefaultNonNull on the *package* (and vice versa). Maybe then it will be simpler
             * to set a proper package default.
             */
            boolean hasNullAwareAnnotation =
                    elt.getAnnotation(DefaultNonNull.class) != null
                            || (elt.getEnclosingElement().getKind() == PACKAGE
                                    && elt.getEnclosingElement().getAnnotation(DefaultNonNull.class)
                                            != null);
            if (hasNullAwareAnnotation) {
                /*
                 * Setting a default here affects not only this element but also its descendants in
                 * the syntax tree.
                 */
                addElementDefault(elt, unionNull, UNBOUNDED_WILDCARD_UPPER_BOUND);
                addElementDefault(elt, noAdditionalNullness, OTHERWISE);
            }

            super.annotate(elt, type);
        }

        @Override
        protected DefaultApplierElement createDefaultApplierElement(
                AnnotatedTypeFactory atypeFactory,
                Element annotationScope,
                AnnotatedTypeMirror type,
                boolean applyToTypeVar) {
            return new DefaultApplierElement(atypeFactory, annotationScope, type, applyToTypeVar) {
                @Override
                protected boolean shouldBeAnnotated(
                        AnnotatedTypeMirror type, boolean applyToTypeVar) {
                    /*
                     * TODO(cpovirk): Are our goals in applying defaults to _all_ type variables compatible
                     * with the goals that the dataflow analysis has in applying defaults to type variables
                     * only if they are the top-level type of a local variable? In particular, are we going to
                     * see problems from our defaulting them to noAdditionalNullness/codeNotNullnessAware,
                     * since it seems as if dataflow would want to default them to TOP (unionNull)? But I'm
                     * not sure where it would even be doing that.
                     */
                    return super.shouldBeAnnotated(type, /*applyToTypeVar=*/ true);
                }
            };
        }

        // TODO(cpovirk): Should I override applyConservativeDefaults to always return false?
    }

    @Override
    protected void addComputedTypeAnnotations(
            Tree tree, AnnotatedTypeMirror type, boolean iUseFlow) {
        // TODO(cpovirk): This helps, but why?
        super.addComputedTypeAnnotations(tree, type, iUseFlow && type.getKind() != WILDCARD);
    }

    @Override
    protected TypeAnnotator createTypeAnnotator() {
        /*
         * Override to:
         *
         * - write some defaults that are common to null-aware and non-null-aware code. Some of
         * these defaults are difficult to express with the @DefaultFor and addElementDefault APIs.
         *
         * - *not* do what the supermethod does. Specifically, the supermethod adds the top type
         * (@Nullable/unionNull) to the bound of unbounded wildcards, but we want the ability to
         * sometimes add @NullnessUnspecified/codeNotNullnessAware instead.
         */
        return new NullSpecTypeAnnotator(this);
    }

    private final class NullSpecTypeAnnotator extends TypeAnnotator {
        NullSpecTypeAnnotator(AnnotatedTypeFactory typeFactory) {
            super(typeFactory);
        }

        @Override
        public Void visitDeclared(AnnotatedDeclaredType type, Void p) {
            AnnotatedDeclaredType enclosingType = type.getEnclosingType();
            if (enclosingType != null) {
                addIfNoAnnotationPresent(enclosingType, noAdditionalNullness);
            }
            return super.visitDeclared(type, p);
        }

        @Override
        public Void visitPrimitive(AnnotatedPrimitiveType type, Void p) {
            addIfNoAnnotationPresent(type, noAdditionalNullness);
            return super.visitPrimitive(type, p);
        }

        @Override
        public Void visitWildcard(AnnotatedWildcardType type, Void p) {
            if (type.getUnderlyingType().getSuperBound() != null) {
                addIfNoAnnotationPresent(type.getExtendsBound(), unionNull);
            }
            return super.visitWildcard(type, p);
        }
    }

    @Override
    protected TreeAnnotator createTreeAnnotator() {
        return new ListTreeAnnotator(
                asList(new NullSpecTreeAnnotator(this), super.createTreeAnnotator()));
    }

    private final class NullSpecTreeAnnotator extends TreeAnnotator {
        NullSpecTreeAnnotator(AnnotatedTypeFactory typeFactory) {
            super(typeFactory);
        }

        @Override
        public Void visitLiteral(LiteralTree node, AnnotatedTypeMirror type) {
            if (node.getKind().asInterface() == LiteralTree.class) {
                type.addAnnotation(
                        node.getKind() == NULL_LITERAL ? unionNull : noAdditionalNullness);
            }

            return super.visitLiteral(node, type);
        }

        @Override
        public Void visitIdentifier(IdentifierTree node, AnnotatedTypeMirror type) {
            annotateIfEnumConstant(node, type);

            return super.visitIdentifier(node, type);
        }

        @Override
        public Void visitMemberSelect(MemberSelectTree node, AnnotatedTypeMirror type) {
            annotateIfEnumConstant(node, type);

            return super.visitMemberSelect(node, type);
        }

        private void annotateIfEnumConstant(ExpressionTree node, AnnotatedTypeMirror type) {
            Element element = elementFromUse(node);
            if (element != null && element.getKind() == ENUM_CONSTANT) {
                /*
                 * Even if it was annotated before, override it. There are 2 cases:
                 *
                 * 1. The declaration had an annotation on it in source. That will still get reported as an
                 * error when we visit the declaration (assuming we're compiling the code with the
                 * declaration): Anything we do here affects the *usage* but not the declaration. And we
                 * know that the usage isn't really @Nullable/@NullnessUnspecified, even if the author of
                 * the declaration said so.
                 *
                 * 2. The declaration had no annotation on it in source, but it was in non-null-aware code.
                 * And consequently, defaults.visit(...), which ran before us, applied a default of
                 * codeNotNullnessAware. Again, that default isn't correct, so we override it here.
                 */
                type.replaceAnnotation(noAdditionalNullness);
            }
        }
    }

    @Override
    protected AnnotationFormatter createAnnotationFormatter() {
        return new DefaultAnnotationFormatter() {
            @Override
            public String formatAnnotationString(
                    Collection<? extends AnnotationMirror> annos, boolean printInvisible) {
                return super.formatAnnotationString(annos, /*printInvisible=*/ false);
            }
        };
    }

    @Override
    protected AnnotatedTypeFormatter createAnnotatedTypeFormatter() {
        return new DefaultAnnotatedTypeFormatter(
                /*
                 * We would pass the result of getAnnotationFormatter(), but the superclass calls
                 * createAnnotatedTypeFormatter() before it initializes that field.
                 *
                 * Fortunately, it's harmless to use one AnnotationFormatter here and another equivalent
                 * one in createAnnotationFormatter().
                 */
                createAnnotationFormatter(),
                // TODO(cpovirk): Permit configuration of these booleans?
                /*printVerboseGenerics=*/ false,
                /*defaultPrintInvisibleAnnos=*/ false);
    }

    private void addIfNoAnnotationPresent(AnnotatedTypeMirror type, AnnotationMirror annotation) {
        if (!type.isAnnotatedInHierarchy(unionNull)) {
            type.addAnnotation(annotation);
        }
    }

    @SuppressWarnings("unchecked") // safety guaranteed by API docs
    private <T extends AnnotatedTypeMirror> T withNoAdditionalNullness(T type) {
        // Remove the annotation from the *root* type, but preserve other annotations.
        type = (T) type.deepCopy(/*copyAnnotations=*/ true);
        type.replaceAnnotation(noAdditionalNullness);
        return type;
    }

    @SuppressWarnings("unchecked") // safety guaranteed by API docs
    private <T extends AnnotatedTypeMirror> T withUnionNull(T type) {
        // Remove the annotation from the *root* type, but preserve other annotations.
        type = (T) type.deepCopy(/*copyAnnotations=*/ true);
        type.replaceAnnotation(unionNull);
        return type;
    }
}
