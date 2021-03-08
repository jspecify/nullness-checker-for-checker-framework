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

import static com.google.jspecify.nullness.Util.IMPLEMENTATION_VARIABLE_LOCATIONS;
import static com.google.jspecify.nullness.Util.nameMatches;
import static com.sun.source.tree.Tree.Kind.NOT_EQUAL_TO;
import static com.sun.source.tree.Tree.Kind.NULL_LITERAL;
import static java.util.Arrays.asList;
import static java.util.Collections.emptyList;
import static java.util.Collections.emptySet;
import static java.util.Collections.singleton;
import static java.util.Collections.singletonList;
import static java.util.Collections.unmodifiableList;
import static javax.lang.model.element.ElementKind.ENUM_CONSTANT;
import static javax.lang.model.type.TypeKind.ARRAY;
import static javax.lang.model.type.TypeKind.DECLARED;
import static javax.lang.model.type.TypeKind.WILDCARD;
import static org.checkerframework.framework.qual.TypeUseLocation.CONSTRUCTOR_RESULT;
import static org.checkerframework.framework.qual.TypeUseLocation.EXCEPTION_PARAMETER;
import static org.checkerframework.framework.qual.TypeUseLocation.IMPLICIT_LOWER_BOUND;
import static org.checkerframework.framework.qual.TypeUseLocation.OTHERWISE;
import static org.checkerframework.framework.qual.TypeUseLocation.RECEIVER;
import static org.checkerframework.framework.util.defaults.QualifierDefaults.AdditionalTypeUseLocation.UNBOUNDED_WILDCARD_UPPER_BOUND;
import static org.checkerframework.javacutil.AnnotationUtils.areSame;
import static org.checkerframework.javacutil.TreeUtils.elementFromDeclaration;
import static org.checkerframework.javacutil.TreeUtils.elementFromUse;
import static org.checkerframework.javacutil.TreeUtils.isNullExpression;
import static org.checkerframework.javacutil.TypesUtils.isPrimitive;
import static org.checkerframework.javacutil.TypesUtils.wildcardToTypeParam;

import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.ClassTree;
import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.IdentifierTree;
import com.sun.source.tree.LambdaExpressionTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.MemberReferenceTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.VariableTree;
import com.sun.tools.javac.code.Type.WildcardType;
import java.lang.annotation.Annotation;
import java.util.Collection;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import javax.lang.model.AnnotatedConstruct;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.Name;
import javax.lang.model.element.TypeParameterElement;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import javax.lang.model.type.TypeVariable;
import javax.lang.model.util.Elements;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.qual.TypeUseLocation;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeFormatter;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedArrayType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedDeclaredType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedIntersectionType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedNoType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedNullType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedPrimitiveType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedTypeVariable;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedUnionType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedWildcardType;
import org.checkerframework.framework.type.DefaultTypeHierarchy;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.NoElementQualifierHierarchy;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.StructuralEqualityComparer;
import org.checkerframework.framework.type.StructuralEqualityVisitHistory;
import org.checkerframework.framework.type.TypeHierarchy;
import org.checkerframework.framework.type.TypeVariableSubstitutor;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.type.typeannotator.TypeAnnotator;
import org.checkerframework.framework.type.visitor.AnnotatedTypeVisitor;
import org.checkerframework.framework.util.AnnotationFormatter;
import org.checkerframework.framework.util.DefaultAnnotationFormatter;
import org.checkerframework.framework.util.DefaultQualifierKindHierarchy;
import org.checkerframework.framework.util.QualifierKindHierarchy;
import org.checkerframework.framework.util.defaults.QualifierDefaults;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.Pair;
import org.jspecify.annotations.DefaultNonNull;
import org.jspecify.annotations.Nullable;
import org.jspecify.annotations.NullnessUnspecified;

final class NullSpecAnnotatedTypeFactory
    extends GenericAnnotatedTypeFactory<
        CFValue, NullSpecStore, NullSpecTransfer, NullSpecAnalysis> {
  // TODO(cpovirk): Consider creating these once and passing them to all other classes.
  private final AnnotationMirror minusNull;
  private final AnnotationMirror unionNull;
  private final AnnotationMirror nullnessOperatorUnspecified;

  private final boolean isLeastConvenientWorld;
  private final NullSpecAnnotatedTypeFactory withLeastConvenientWorld;
  private final NullSpecAnnotatedTypeFactory withMostConvenientWorld;

  /** Constructor that takes all configuration from the provided {@code checker}. */
  NullSpecAnnotatedTypeFactory(BaseTypeChecker checker) {
    this(checker, checker.hasOption("strict"), /*withOtherWorld=*/ null);
  }

  /**
   * Constructor that takes all configuration from the provided {@code checker} <i>except</i> {@code
   * strict}/{@code isLeastConvenientWorld}. It also accepts another instance of this class (if one
   * is already available) that represents the other "world."
   */
  private NullSpecAnnotatedTypeFactory(
      BaseTypeChecker checker,
      boolean isLeastConvenientWorld,
      NullSpecAnnotatedTypeFactory withOtherWorld) {
    // Only use flow-sensitive type refinement if implementation code should be checked
    super(checker, checker.hasOption("checkImpl"));

    /*
     * Under our proposed subtyping rules, every type has a "nullness operator." There are 4
     * nullness-operator values. In this implementation, we *mostly* represent each one with an
     * AnnotationMirror.
     *
     * There is one exception: We do not have an AnnotationMirror for the nullness operator
     * NO_CHANGE. When we need to represent NO_CHANGE, we take one of two approaches, depending on
     * the base type:
     *
     * - On type-variable usage, we use *no* annotation.
     *
     * - On other types, we use minusNull.
     *
     * For further discussion of this, see isNullExclusiveUnderEveryParameterization.
     *
     * Since the proposed subtyping rules use names like "CODE_NOT_NULLNESS_AWARE," we follow those
     * names here. That way, we distinguish more clearly between "Does a type have a
     * @NullnessUnspecified annotation written on it in source code?" and "Is the nullness operator
     * of a type nullnessOperatorUnspecified?" (The latter can happen not only from a
     * @NullnessUnspecified annotation but also from the default in effect.)
     */
    minusNull = AnnotationBuilder.fromClass(elements, MinusNull.class);
    unionNull = AnnotationBuilder.fromClass(elements, Nullable.class);
    nullnessOperatorUnspecified = AnnotationBuilder.fromClass(elements, NullnessUnspecified.class);
    /*
     * Note that all the above annotations must be on the *classpath*, not just the *processorpath*.
     * That's because, even if we change fromClass to fromName, AnnotationBuilder ultimately calls
     * elements.getTypeElement.
     *
     * For Nullable, that's perhaps tolerable, though not ideal: Any invocation of the checker will
     * need to include the JSpecify annotations jar on the classpath, even if the annotations don't
     * appear in any of the sources or libraries.
     *
     * For MinusNull, it's worse: Since MinusNull doesn't exist in the *annotations* jar (since we
     * aren't exposing it to end users, at least currently), checker invocations must put the
     * *checker* jar on the *classpath* (not just the processorpath). Perhaps we should include
     * MinusNull in the annotations jar (as a package-private class that the checker refers to only
     * by name, including looking up reflectively in createSupportedTypeQualifiers?)? It would be
     * nice if we didn't need a full AnnotationMirror at all, only a class name, but
     * AnnotationMirror is baked into CF deeply, since CF needs to support generalized annotation
     * types, write annotations back to bytecode, and perhaps more.
     *
     * For NullnessUnspecified, it depends on whether we expose NullnessUnspecified to users or not:
     * If we do, then it's like Nullable. If we don't, then it's like MinusNull.
     *
     * TODO(cpovirk): See if we can avoid requiring the checker on the classpath.
     */

    if (checker.hasOption("aliasCFannos")) {
      addAliasedTypeAnnotation(
          org.checkerframework.checker.nullness.qual.Nullable.class, unionNull);
    }

    this.isLeastConvenientWorld = isLeastConvenientWorld;

    postInit();

    /*
     * Creating a new AnnotatedTypeFactory is expensive -- especially parseStubFiles. So we make
     * sure to create only a single instance for each "world."
     *
     * It would be better if we could operate in both "worlds" without needing to create 2 separate
     * AnnotatedTypeFactory instances. But I worry about accidentally depending on state that is
     * specific to the world that the current instance was created with.
     */
    if (withOtherWorld == null) {
      withOtherWorld =
          new NullSpecAnnotatedTypeFactory(
              checker, !isLeastConvenientWorld, /*withOtherWorld=*/ this);
    }
    if (isLeastConvenientWorld) {
      withLeastConvenientWorld = this;
      withMostConvenientWorld = withOtherWorld;
    } else {
      withLeastConvenientWorld = withOtherWorld;
      withMostConvenientWorld = this;
    }
  }

  @Override
  protected Set<Class<? extends Annotation>> createSupportedTypeQualifiers() {
    return new LinkedHashSet<>(asList(Nullable.class, NullnessUnspecified.class, MinusNull.class));
  }

  @Override
  protected QualifierHierarchy createQualifierHierarchy() {
    return new NullSpecQualifierHierarchy(getSupportedTypeQualifiers(), elements);
  }

  private final class NullSpecQualifierHierarchy extends NoElementQualifierHierarchy {
    NullSpecQualifierHierarchy(
        Collection<Class<? extends Annotation>> qualifierClasses, Elements elements) {
      super(qualifierClasses, elements);
    }

    @Override
    public boolean isSubtype(AnnotationMirror subAnno, AnnotationMirror superAnno) {
      /*
       * Since we perform all necessary checking in the isSubtype method in NullSpecTypeHierarchy, I
       * tried replacing this body with `return true` to avoid duplicating logic. However, that's a
       * problem because the result of this method is sometimes cached and used instead of a full
       * call to the isSubtype method in NullSpecTypeHierarchy.
       *
       * Specifically: DefaultTypeHierarchy.visitDeclared_Declared calls isPrimarySubtype, which
       * calls isAnnoSubtype, which directly calls NullSpecQualifierHierarchy.isSubtype (as opposed
       * to NullSpecTypeHierarchy.isSubtype). That's still fine, since we'll reject the types in
       * NullSpecTypeHierarchy.isSubtype. The problem, though, is that it also inserts a cache entry
       * for the supposed subtyping relationship, and that entry can cause future checks to
       * short-circuit. (I think I saw this in isContainedBy.)
       */
      boolean subIsUnspecified = areSame(subAnno, nullnessOperatorUnspecified);
      boolean superIsUnspecified = areSame(superAnno, nullnessOperatorUnspecified);
      boolean eitherIsUnspecified = subIsUnspecified || superIsUnspecified;
      boolean bothAreUnspecified = subIsUnspecified && superIsUnspecified;
      if (isLeastConvenientWorld && bothAreUnspecified) {
        return false;
      }
      if (!isLeastConvenientWorld && eitherIsUnspecified) {
        return true;
      }
      return areSame(subAnno, minusNull) || areSame(superAnno, unionNull);
    }

    @Override
    protected QualifierKindHierarchy createQualifierKindHierarchy(
        Collection<Class<? extends Annotation>> qualifierClasses) {
      return new DefaultQualifierKindHierarchy(qualifierClasses, /*bottom=*/ MinusNull.class) {
        @Override
        protected Map<DefaultQualifierKind, Set<DefaultQualifierKind>> createDirectSuperMap() {
          DefaultQualifierKind minusNullKind =
              nameToQualifierKind.get(MinusNull.class.getCanonicalName());
          DefaultQualifierKind unionNullKind =
              nameToQualifierKind.get(Nullable.class.getCanonicalName());
          DefaultQualifierKind nullnessOperatorUnspecified =
              nameToQualifierKind.get(NullnessUnspecified.class.getCanonicalName());

          Map<DefaultQualifierKind, Set<DefaultQualifierKind>> supers = new HashMap<>();
          supers.put(minusNullKind, singleton(nullnessOperatorUnspecified));
          supers.put(nullnessOperatorUnspecified, singleton(unionNullKind));
          supers.put(unionNullKind, emptySet());
          return supers;
          /*
           * The rules above are incomplete:
           *
           * - In "lenient mode," we treat unionNull as a subtype of codeNotNullnesesAware.
           *
           * - In "strict mode," we do *not* treat codeNotNullnesesAware as a subtype of itself.
           *
           * These subtleties are handled by isSubtype above. The incomplete rules still provide us
           * with useful implementations of leastUpperBound and greatestLowerBound.
           */
        }
      };
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
      return new NullSpecEqualityComparer(areEqualVisitHistory);
    }

    @Override
    protected boolean visitTypevarSubtype(
        AnnotatedTypeVariable subtype, AnnotatedTypeMirror supertype) {
      /*
       * The superclass "projects" type-variable usages rather than unioning them. Consequently, if
       * we delegate directly to the supermethod, it can fail when it shouldn't.  Fortunately, we
       * already handle the top-level nullness subtyping in isNullnessSubtype. So all we need to do
       * here is to handle any type arguments. To do that, we still delegate to the supertype. But
       * first we mark the supertype as unionNull so that the supertype's top-level check will
       * always succeed.
       *
       * TODO(cpovirk): There are probably many more cases that we could short-circuit. We might
       * consider doing that in isSubtype rather than with overrides.
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
       * TODO(cpovirk): Why are the supertype cases so different from the subtype cases above? In
       * particular: Why is it important to replace the subtype instead of the supertype?
       */
      return super.visitTypevarSupertype(withMinusNull(subtype), supertype);
    }

    @Override
    protected boolean visitWildcardSupertype(
        AnnotatedTypeMirror subtype, AnnotatedWildcardType supertype) {
      /*
       * See discussion in visitTypevarSupertype above.
       *
       * Plus: TODO(cpovirk): Why is it important to replace an argument only conditionally?
       */
      return super.visitWildcardSupertype(
          isNullInclusiveUnderEveryParameterization(supertype) ? withMinusNull(subtype) : subtype,
          supertype);
    }

    @Override
    public Boolean visitTypevar_Typevar(
        AnnotatedTypeVariable subtype, AnnotatedTypeVariable supertype, Void p) {
      /*
       * Everything we need to check will be handled by isNullnessSubtype. That's fortunate, as the
       * supermethod does not account for our non-standard substitution rules for type variables.
       * Under those rules, `@NullnessUnspecified T` can still produce a @Nullable value after
       * substitution.
       */
      return true;
    }

    @Override
    protected boolean isSubtype(
        AnnotatedTypeMirror subtype, AnnotatedTypeMirror supertype, AnnotationMirror top) {
      return super.isSubtype(subtype, supertype, top) && isNullnessSubtype(subtype, supertype);
    }

    private boolean isNullnessSubtype(AnnotatedTypeMirror subtype, AnnotatedTypeMirror supertype) {
      if (isPrimitive(subtype.getUnderlyingType())) {
        return true;
      }
      if (supertype.getKind() == WILDCARD) {
        /*
         * super.isSubtype already called back into this.isSameType (and thus into
         * isNullnessSubtype) for the bound. That's fortunate, as we don't define subtyping rules
         * for wildcards (since the JLS says that they should be capture converted by this point, or
         * we should be checking their *bounds* for a containment check).
         */
        return true;
      }
      if (subtype instanceof AnnotatedWildcardType
          && ((AnnotatedWildcardType) subtype).isUninferredTypeArgument()) {
        /*
         * Hope for the best, as the supertype does.
         *
         * XXX: I'm not sure if I'm exactly matching the cases in which the supertype checks for
         * uninferred type arguments. But this check is enough to eliminate the compile errors I was
         * seeing in my testing and also not so much that it breaks handling of any of our existing
         * samples.
         */
        return true;
      }
      return isNullInclusiveUnderEveryParameterization(supertype)
          || isNullExclusiveUnderEveryParameterization(subtype)
          || nullnessEstablishingPathExists(subtype, supertype);
    }
  }

  boolean isNullInclusiveUnderEveryParameterization(AnnotatedTypeMirror type) {
    /*
     * Our draft subtyping rules specify a special case for intersection types. However, those rules
     * make sense only because the rules also specify that an intersection type never has an
     * nullness-operator value of its own. This is in contrast to CF, which does let an intersection
     * type have an AnnotationMirror of its own.
     *
     * ...well, sort of. As I understand it, what CF does is more that it tries to keep the
     * AnnotationMirror of the intersecton type in sync with the AnnotationMirror of each of its
     * components (which should themselves all match). So the intersection type "has" an
     * AnnotationMirror, but it provides no *additional* information beyond what is already carried
     * by its components' AnnotationMirrors.
     *
     * Nevertheless, the result is that we don't need a special case here: The check below is
     * redundant with the subsequent check on the intersection's components, but redundancy is
     * harmless.
     */
    return type.hasAnnotation(unionNull)
        || (!isLeastConvenientWorld && type.hasAnnotation(nullnessOperatorUnspecified));
  }

  boolean isNullExclusiveUnderEveryParameterization(AnnotatedTypeMirror type) {
    return nullnessEstablishingPathExists(
        type, t -> t.getKind() == DECLARED || t.getKind() == ARRAY);
  }

  private boolean nullnessEstablishingPathExists(
      AnnotatedTypeMirror subtype, AnnotatedTypeMirror supertype) {
    /*
     * TODO(cpovirk): As an optimization, `return false` if `supertype` is not a type variable: If
     * it's not a type variable, then the only ways for isNullnessSubtype to succeed were already
     * checked by isNullInclusiveUnderEveryParameterization and
     * isNullExclusiveUnderEveryParameterization.
     */
    return nullnessEstablishingPathExists(
        subtype, t -> checker.getTypeUtils().isSameType(t, supertype.getUnderlyingType()));
  }

  private boolean nullnessEstablishingPathExists(
      AnnotatedTypeMirror subtype, Predicate<TypeMirror> supertypeMatcher) {
    /*
     * In most cases, we do not need to check specifically for minusNull because the remainder of
     * the method is sufficient. However, consider a type that meets all 3 of the following
     * criteria:
     *
     * 1. a local variable
     *
     * 2. whose type is a type variable
     *
     * 3. whose corresponding type parameter permits nullable type arguments
     *
     * For such a type, the remainder of the method would always return false. And that makes
     * sense... until an implementation checks it with `if (foo != null)`. At that point, we need to
     * store an additional piece of information: Yes, _the type written in code_ can permit null,
     * but we know from dataflow that _this particular value_ is _not_ null. That additional
     * information is stored by attaching minusNull to the type-variable usage. This produces a type
     * distinct from all of:
     *
     * - `T`: `T` with nullness operator NO_CHANGE
     *
     * - `@NullnessUnspecified T`: `T` with nullness operator CODE_NOT_NULLNESS_AWARE
     *
     * - `@Nullable T`: `T` with nullness operator UNION_NULL
     *
     * It is unfortunate that this forces us to represent type-variable usages differently from how
     * we represent all other types. For all other types, the way to represent a type with nullness
     * operator NO_CHANGE is to attach minusNull. But again, for type-variable usages, the way to do
     * it is to attach *no* annotation.
     *
     * TODO(cpovirk): Is the check for minusNull also important for the special case of minusNull
     * type-variable usages generated by substituteTypeVariable? If so, add a sample input that
     * demonstrates it.
     */
    if (subtype.hasAnnotation(minusNull)) {
      return true;
    }

    if (isUnionNullOrEquivalent(subtype)) {
      return false;
    }

    /*
     * The following special case for type variables works around a problem with CF defaulting: When
     * CF computes the default for the bound of a type-variable usage, it uses the defaulting rules
     * that are in effect at the site of the usage. It probably should instead use the defaulting
     * rules that are in effect at the site of the type-parameter declaration. To get the rules we
     * want, we look up the type of the declaration element. (But first we do look at the use site a
     * little, just to make sure that it's not `@Nullable E` (or `@NullnessUnspecified E`, if in the
     * least convenient world).)
     *
     * See https://github.com/typetools/checker-framework/issues/3845
     *
     * TODO(cpovirk): I fear that this workaround may have problems of its own: We really want the
     * parameter declaration _as a member of the declaration we're working with_. The stock CF
     * behavior would give us much of this for free by carrying the bounds along with the
     * type-variable usage, substituting as it goes. Perhaps we need for AnnotatedTypeVariable to
     * carry a list of substitution operations along with it, which this code would apply when it
     * looks up the bounds? But ideally the CF issue will have a more principled solution, at which
     * point we could fall back to using stock CF behavior.
     */
    if (subtype instanceof AnnotatedTypeVariable) {
      AnnotatedTypeVariable variable = (AnnotatedTypeVariable) subtype;
      subtype = getAnnotatedType(variable.getUnderlyingType().asElement());
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
     * We don't need to handle the "lower-bound rule" here: The Checker Framework doesn't perform
     * wildcard capture conversion. (Hmm, but it might see post-capture-conversion types in some
     * cases....) It compares "? super Foo" against "Bar" by more directly comparing Foo and Bar.
     */
    return false;
  }

  private List<? extends AnnotatedTypeMirror> getUpperBounds(AnnotatedTypeMirror type) {
    switch (type.getKind()) {
      case INTERSECTION:
        return ((AnnotatedIntersectionType) type).getBounds();

      case TYPEVAR:
        return singletonList(((AnnotatedTypeVariable) type).getUpperBound());

      case WILDCARD:
        AnnotatedWildcardType asWildcard = (AnnotatedWildcardType) type;
        return unmodifiableList(
            asList(
                asWildcard.getExtendsBound(),
                /*
                 * TODO(cpovirk): This is similar to the special case for AnnotatedTypeVariable in
                 * nullnessEstablishingPathExists: It lets us apply proper defaulting but at the
                 * cost of losing substitution.
                 */
                ((AnnotatedTypeVariable) getAnnotatedType(correspondingTypeParameter(asWildcard)))
                    .getUpperBound()));

      default:
        return emptyList();
    }
  }

  private boolean isUnionNullOrEquivalent(AnnotatedTypeMirror type) {
    return type.hasAnnotation(unionNull)
        || (isLeastConvenientWorld && type.hasAnnotation(nullnessOperatorUnspecified));
  }

  private final class NullSpecEqualityComparer extends StructuralEqualityComparer {
    NullSpecEqualityComparer(StructuralEqualityVisitHistory typeargVisitHistory) {
      super(typeargVisitHistory);
    }

    @Override
    protected boolean checkOrAreEqual(AnnotatedTypeMirror type1, AnnotatedTypeMirror type2) {
      Boolean pastResult = visitHistory.get(type1, type2, /*hierarchy=*/ unionNull);
      if (pastResult != null) {
        return pastResult;
      }

      boolean result = areEqual(type1, type2);
      this.visitHistory.put(type1, type2, /*hierarchy=*/ unionNull, result);
      return result;
    }

    @Override
    public boolean areEqualInHierarchy(
        AnnotatedTypeMirror type1, AnnotatedTypeMirror type2, AnnotationMirror top) {
      return areEqual(type1, type2);
    }

    private boolean areEqual(AnnotatedTypeMirror type1, AnnotatedTypeMirror type2) {
      /*
       * Eventually, we'll test the spec definition: "type1 is a subtype of type2 and vice versa."
       * However, we perform some other tests first. Why?
       *
       * Well, originally, testing the spec definition somehow produced infinite recursion. (I don't
       * think the spec requires infinite recursion; I think the implementation just produced it
       * somehow, though I don't recall how.) When that happened, I switched to not using the spec
       * definition _at all_. However, I don't see infinite recursion anymore (with any of our
       * samples or with Guava), even if I use that definition exclusively. I remain a _little_
       * nervous about switching to using the spec definition exclusively -- or even using it
       * conditionally, as we do now -- but it's _probably_ safe.
       *
       * But we still can't rely solely on the spec definition, at least at present. If we try to,
       * we produce errors for samples like the following:
       *
       * https://github.com/jspecify/jspecify/blob/5f67b5e2388adc6e1ce386bf7957eef588d981db/samples/OverrideParametersThatAreTypeVariables.java#L41
       *
       * I think that is because of the somewhat odd contract for this method, as described into the
       * TODO at the end of this method: The method is not actually _supposed_ to check that the
       * given _types_ are equal, only that... their primary annotations are? Or something?
       *
       * TODO(cpovirk): Even if we're keeping both checks, it seems like _some_ of the code below
       * may be redundant (or even wrong).
       */
      boolean type1IsUnspecified = type1.hasAnnotation(nullnessOperatorUnspecified);
      boolean type2IsUnspecified = type2.hasAnnotation(nullnessOperatorUnspecified);
      boolean bothAreUnspecified = type1IsUnspecified && type2IsUnspecified;
      boolean eitherIsUnspecified = type1IsUnspecified || type2IsUnspecified;
      if (isLeastConvenientWorld && bothAreUnspecified) {
        return false;
      }
      if (!isLeastConvenientWorld && eitherIsUnspecified) {
        return true;
      }
      AnnotationMirror a1 = type1.getAnnotationInHierarchy(unionNull);
      AnnotationMirror a2 = type2.getAnnotationInHierarchy(unionNull);
      if (a1 == a2) {
        return true;
      }
      if (a1 != null && a2 != null && areSame(a1, a2)) {
        return true;
      }
      if (withLeastConvenientWorld().isNullExclusiveUnderEveryParameterization(type1)
          && withLeastConvenientWorld().isNullExclusiveUnderEveryParameterization(type2)) {
        /*
         * One is `T`, and the other is `@MinusNull T`, and `T` has a non-nullable bound. Thus, the
         * two are effectively the same.
         *
         * TODO(cpovirk): Why do we sometimes end up with one of those and sometimes with the other?
         * Can we ensure that we always end up with `@MinusNull T`? Alternatively, can we avoid
         * creating `@MinusNull T` when `T` is already known to be non-nullable? And whether we
         * leave this code in or replace it with other code, do we need to update our subtyping
         * rules to reflect this case?
         */
        return true;
      }
      return getTypeHierarchy().isSubtype(type1, type2)
          && getTypeHierarchy().isSubtype(type2, type1);
      /*
       * TODO(cpovirk): Do we care about the base type, or is looking at annotations enough?
       * super.visitDeclared_Declared has a TODO with a similar question. Err, presumably normal
       * Java type-checking has done that job. A more interesting question may be why we don't look
       * at type args. The answer might be simply: "That's the contract, even though it is
       * surprising, given the names of the class and its methods." (Granted, the docs of
       * super.visitDeclared_Declared also say that it checks that "The types are of the same
       * class/interfaces," so the contract isn't completely clear.)
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
      AnnotatedTypeMirror substitute = argument.deepCopy(/*copyAnnotations=*/ true);

      /*
       * The isNullExclusiveUnderEveryParameterization check handles cases like
       * `ImmutableList.Builder<E>` in non-null-aware code: Technically, we aren't sure if the
       * non-null-aware class might be instantiated with a nullable argument for E. But we know
       * that, no matter what, if someone calls `listBuilder.add(null)`, that is bad. So we treat
       * the declaration as if it said `ImmutableList.Builder<@MinusNull E>`.
       */
      if (withLeastConvenientWorld().isNullExclusiveUnderEveryParameterization(use)) {
        substitute.replaceAnnotation(minusNull);
      } else if (argument.hasAnnotation(unionNull) || use.hasAnnotation(unionNull)) {
        substitute.replaceAnnotation(unionNull);
      } else if (argument.hasAnnotation(nullnessOperatorUnspecified)
          || use.hasAnnotation(nullnessOperatorUnspecified)) {
        substitute.replaceAnnotation(nullnessOperatorUnspecified);
      }

      return substitute;
    }
  }

  @Override
  public NullSpecTransfer createFlowTransferFunction(
      CFAbstractAnalysis<CFValue, NullSpecStore, NullSpecTransfer> analysis) {
    return new NullSpecTransfer(analysis);
  }

  @Override
  public AnnotatedDeclaredType getSelfType(Tree tree) {
    AnnotatedDeclaredType superResult = super.getSelfType(tree);
    return superResult == null ? null : withMinusNull(superResult);
  }

  @Override
  protected void addCheckedStandardDefaults(QualifierDefaults defs) {
    /*
     * Override to *not* call the supermethod. The supermethod would set up CLIMB defaults, which we
     * don't want.
     *
     * Furthermore, while we do want defaults of our own, we don't set them here. In particular, we
     * don't call defs.addCheckedCodeDefault(nullnessOperatorUnspecified, OTHERWISE). If we did,
     * then that default would be applied to all unannotated type-variable usages, even in
     * null-aware code. That's because there are multiple rounds of defaulting, 2 of which interact
     * badly:
     *
     * The first round of the 2 to run is per-element defaulting. That includes our null-aware
     * defaulting logic. (See populateNewDefaults below.) That defaulting logic would leave
     * type-variable usages unannotated.
     *
     * The later round to run is checkedCodeDefaults (which would include any defaults set by this
     * method). That logic would find the type-variable usages unannotated. So, if that logic put
     * nullnessOperatorUnspecified on all unannotated type-variable usages, it would really put it
     * on *all* unannotated type-variable usages -- even the ones in null-aware code.
     *
     * To avoid that, we set *all* defaults as per-element defaults. That setup eliminates the
     * second round entirely. Thus, defaulting runs a single time for a given type usage. So, when
     * the null-aware logic declines to annotate a type-variable usage, it stays unannotated
     * afterward.
     *
     * The stock CF does not have this problem because it hass no such thing as a per-element
     * default of "do not annotate this" that overrides a checkedCodeDefaults default of "do
     * annotate this."
     */
  }

  @Override
  protected void checkForDefaultQualifierInHierarchy(QualifierDefaults defs) {
    /*
     * We don't set normal checkedCodeDefaults. This method would report that lack of defaults as a
     * problem. That's because CF wants to ensure that every[*] type usage is annotated.
     *
     * However, we *do* ensure that every[*] type usage is annotated. To do so, we always set a
     * default for OTHERWISE on top-level elements. (We do this in populateNewDefaults.) See further
     * discussion in addCheckedStandardDefaults.
     *
     * So, we override this method to not report a problem.
     *
     * [*] There are a few exceptions that we don't need to get into here.
     */
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
    protected void populateNewDefaults(Element elt, boolean initialDefaultsAreEmpty) {
      /*
       * Note: This method does not contain the totality of our defaulting logic. For example, our
       * TypeAnnotator has special logic for upper bounds _in the case of `super` wildcards
       * specifically_.
       *
       * Note: Setting a default here affects not only this element but also its descendants in the
       * syntax tree.
       */
      if (hasNullAwareOrEquivalent(elt)) {
        addElementDefault(elt, unionNull, UNBOUNDED_WILDCARD_UPPER_BOUND);
        addElementDefault(elt, minusNull, OTHERWISE);
        addDefaultToTopForLocationsRefinedByDataflow(elt);
        /*
         * (For any TypeUseLocation that we don't set an explicit value for, we inherit any value
         * from the enclosing element, which might be a non-null-aware element. That's fine: While
         * our non-null-aware setup sets defaults for more locations than just these, it sets those
         * locations' defaults to minusNull -- matching the value that we want here.)
         */
      } else if (initialDefaultsAreEmpty) {
        /*
         * We need to set defaults appropriate to non-null-aware code. In a normal checker, we would
         * expect for such "default defaults" to be set in addCheckedStandardDefaults. But we do
         * not, as discussed in our implementation of that method.
         */

        // Here's the big default, the "default default":
        addElementDefault(elt, nullnessOperatorUnspecified, OTHERWISE);

        // Some locations are intrinsically non-nullable:
        addElementDefault(elt, minusNull, CONSTRUCTOR_RESULT);
        addElementDefault(elt, minusNull, RECEIVER);

        // We do want *some* of the CLIMB standard defaults:
        addDefaultToTopForLocationsRefinedByDataflow(elt);
        addElementDefault(elt, minusNull, IMPLICIT_LOWER_BOUND);

        /*
         * But note one difference from the CLIMB defaults: We want the default for implicit upper
         * bounds to match the "default default" of nullnessOperatorUnspecified, not to be
         * top/unionNull. We accomplished this already simply by not making our
         * addCheckedStandardDefaults implementation call its supermethod (which would otherwise
         * call addClimbStandardDefaults, which would override the "default default").
         */
      }
    }

    private void addDefaultToTopForLocationsRefinedByDataflow(Element elt) {
      for (TypeUseLocation location : IMPLEMENTATION_VARIABLE_LOCATIONS) {
        /*
         * Handling exception parameters correctly is hard, so just treat them as if they're
         * restricted to non-null values. Of course the caught exception is already non-null, so all
         * this does is forbid users from manually assigning null to an exception parameter.
         */
        if (location == EXCEPTION_PARAMETER) {
          addElementDefault(elt, minusNull, location);
        } else {
          addElementDefault(elt, unionNull, location);
        }
      }
    }

    @Override
    protected boolean shouldAnnotateOtherwiseNonDefaultableTypeVariable(AnnotationMirror qual) {
      /*
       * CF usually doesn't apply defaults to type-variable usages. But in non-null-aware code, we
       * want our default of nullnessOperatorUnspecified to apply even to type variables.
       *
       * But there are 2 other things to keep in mind:
       *
       * - CF *does* apply defaults to type-variable usages *if* they are local variables. That's
       * because it will refine their types with dataflow. This CF behavior works fine for us: Since
       * we want to apply defaults in strictly more cases, we're happy to accept what CF already
       * does for local variables. (We do need to be sure to apply unionNull (our top type) in that
       * case, rather than nullnessOperatorUnspecified. We accomplish that in
       * addDefaultToTopForLocationsRefinedByDataflow.)
       *
       * - Non-null-aware code (discussed above) is easy: We apply nullnessOperatorUnspecified to
       * everything except local variables. But null-aware code more complex. First, set aside local
       * variables, which we handle as discussed above. After that, we need to apply minusNull to
       * most types, but we need to *not* apply it to (non-local-variable) type-variable usages.
       * (For more on this, see isNullExclusiveUnderEveryParameterization.) This need is weird
       * enough that stock CF doesn't appear to support it. Our solution is to introduce this hook
       * method into our CF fork and then override it here. Our solution also requires that we set
       * up defaulting in a non-standard way, as discussed in addCheckedStandardDefaults and other
       * locations.
       */
      return areSame(qual, nullnessOperatorUnspecified);
    }

    @Override
    public boolean applyConservativeDefaults(Element annotationScope) {
      /*
       * Ignore any command-line flag to request conservative defaults. The principle of
       * "unspecified nullness" is that we configure conservatism/leniency through changes in our
       * subtyping rules, rather than changes in how we choose the default annotation / nullness
       * operator of any type.
       */
      return false;
    }
  }

  @Override
  protected void addComputedTypeAnnotations(Tree tree, AnnotatedTypeMirror type, boolean iUseFlow) {
    /*
     * TODO(cpovirk): Eliminate this workaround. But currently, it helps in some of our samples and
     * in Guava, though I am unsure why. The problem it works around may well be caused by our
     * failure to keep wildcards' annotations in sync with their bounds' annotations (whereas stock
     * CF does).
     *
     * Note that this workaround also hurts: See the comment that mentions it in
     * NullSpecTransfer.refineFutureMapGetFromMapContainsKey.
     */
    super.addComputedTypeAnnotations(tree, type, iUseFlow && type.getKind() != WILDCARD);
  }

  @Override
  protected TypeAnnotator createTypeAnnotator() {
    /*
     * Override to:
     *
     * - write some defaults that are difficult to express with the addCheckedCodeDefault and
     * addElementDefault APIs. But beware: Using TypeAnnotator for this purpose is safe only for
     * defaults that are common to null-aware and non-null-aware code!
     *
     * - *not* do what the supermethod does. I don't fully understand what the supermethod's
     * PropagationTypeAnnotator does, but here's part of what I think it does: It overwrites the
     * annotations on upper bounds of unbounded wildcards to match those on their corresponding type
     * parameters. This means that it overwrites our not-null-aware default bound of
     * @NullnessUnspecified. But I also seem to be seeing problems in the *reverse* direction, and I
     * understand those even less. (To be fair, our entire handling of upper bounds of unbounded
     * wildcards is a hack: The normal CF quite reasonably doesn't want for them to have bounds of
     * their own, but we do.) Sadly, it turns out that the supermethod's effects are sometimes
     * *desirable*, so this workaround causes issues of its own....
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
        /*
         * TODO(cpovirk): If NullSpecVisitor starts looking at source trees instead of the derived
         * AnnotatedTypeMirror objects, then change this code to fill in this value unconditionally
         * (matching visitPrimitive below).
         */
        addIfNoAnnotationPresent(enclosingType, minusNull);
      }
      return super.visitDeclared(type, p);
    }

    @Override
    public Void visitPrimitive(AnnotatedPrimitiveType type, Void p) {
      type.replaceAnnotation(minusNull);
      return super.visitPrimitive(type, p);
    }

    @Override
    public Void visitWildcard(AnnotatedWildcardType type, Void p) {
      if (type.getUnderlyingType().getSuperBound() != null) {
        addIfNoAnnotationPresent(type.getExtendsBound(), unionNull);
      }
      return super.visitWildcard(type, p);
    }

    @Override
    public Void visitExecutable(AnnotatedExecutableType type, Void p) {
      /*
       * This implements a limited degree of support for declaration annotations. Assumptions
       * include:
       *
       * - ProtoNonnullApi really guarantees that *all* types are non-null, even those that would
       * require type annotations to annotate.
       *
       * - Any ProtoMethodMayReturnNull or ProtoMethodAcceptsNullParameter annotation on an array
       * applies to the array as a whole, not to the element type.
       *
       * - maybe other things?
       *
       * I suspect that the edge cases don't come up in the simple case of protos, but this may need
       * more investigation.
       */
      ExecutableElement method = type.getElement();
      if (hasAnnotationInCode(method, "ProtoMethodMayReturnNull")) {
        type.getReturnType().replaceAnnotation(unionNull);
      }
      for (int i = 0; i < type.getParameterTypes().size(); i++) {
        AnnotatedTypeMirror parameterType = type.getParameterTypes().get(i);
        VariableElement parameter = method.getParameters().get(i);
        if (hasAnnotationInCode(parameter, "ProtoMethodAcceptsNullParameter")) {
          parameterType.replaceAnnotation(unionNull);
        }
      }
      return super.visitExecutable(type, p);
    }
  }

  @Override
  protected TreeAnnotator createTreeAnnotator() {
    return new ListTreeAnnotator(new NullSpecTreeAnnotator(this), super.createTreeAnnotator());
  }

  private final class NullSpecTreeAnnotator extends TreeAnnotator {
    NullSpecTreeAnnotator(AnnotatedTypeFactory typeFactory) {
      super(typeFactory);
    }

    @Override
    public Void visitLiteral(LiteralTree tree, AnnotatedTypeMirror type) {
      if (tree.getKind().asInterface() == LiteralTree.class) {
        type.addAnnotation(tree.getKind() == NULL_LITERAL ? unionNull : minusNull);
      }

      return super.visitLiteral(tree, type);
    }

    @Override
    public Void visitBinary(BinaryTree tree, AnnotatedTypeMirror type) {
      type.addAnnotation(minusNull);
      return super.visitBinary(tree, type);
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree tree, AnnotatedTypeMirror type) {
      if (establishesStreamElementsAreNonNull(tree)) {
        AnnotatedTypeMirror returnedStreamElementType =
            ((AnnotatedDeclaredType) type).getTypeArguments().get(0);
        returnedStreamElementType.replaceAnnotation(minusNull);
      }

      return super.visitMethodInvocation(tree, type);
    }

    private boolean establishesStreamElementsAreNonNull(ExpressionTree tree) {
      if (!(tree instanceof MethodInvocationTree)) {
        return false;
      }
      MethodInvocationTree invocation = (MethodInvocationTree) tree;
      ExecutableElement method = elementFromUse(invocation);
      if (!nameMatches(method, "Stream", "filter")) {
        return false;
      }
      ExpressionTree predicate = invocation.getArguments().get(0);
      if (predicate instanceof MemberReferenceTree) {
        MemberReferenceTree memberReferenceTree = (MemberReferenceTree) predicate;
        /*
         * TODO(cpovirk): Ensure that it's java.lang.Class.isInstance or java.util.Objects.nonNull
         * specifically.
         */
        return memberReferenceTree.getName().contentEquals("isInstance")
            || memberReferenceTree.getName().contentEquals("nonNull");
      } else if (predicate instanceof LambdaExpressionTree) {
        LambdaExpressionTree lambdaExpressionTree = (LambdaExpressionTree) predicate;
        if (lambdaExpressionTree.getBody().getKind() == NOT_EQUAL_TO) {
          VariableTree lambdaParameter = lambdaExpressionTree.getParameters().get(0);
          BinaryTree binaryTree = (BinaryTree) lambdaExpressionTree.getBody();
          ExpressionTree left = binaryTree.getLeftOperand();
          ExpressionTree right = binaryTree.getRightOperand();
          return areNullAndLambdaParameter(left, right, lambdaParameter)
              || areNullAndLambdaParameter(right, left, lambdaParameter);
        }
        return false;
      } else {
        return false;
      }
    }

    private boolean areNullAndLambdaParameter(
        ExpressionTree u, ExpressionTree v, VariableTree lambdaParameter) {
      return isNullExpression(u) && elementFromUse(v) == elementFromDeclaration(lambdaParameter);
    }

    @Override
    public Void visitIdentifier(IdentifierTree tree, AnnotatedTypeMirror type) {
      annotateIfEnumConstant(tree, type);

      return super.visitIdentifier(tree, type);
    }

    @Override
    public Void visitMemberSelect(MemberSelectTree tree, AnnotatedTypeMirror type) {
      annotateIfEnumConstant(tree, type);

      return super.visitMemberSelect(tree, type);
    }

    private void annotateIfEnumConstant(ExpressionTree tree, AnnotatedTypeMirror type) {
      Element element = elementFromUse(tree);
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
         * nullnessOperatorUnspecified. Again, that default isn't correct, so we override it here.
         */
        type.replaceAnnotation(minusNull);
      }
    }
  }

  @Override
  protected NullSpecAnalysis createFlowAnalysis(List<Pair<VariableElement, CFValue>> fieldValues) {
    return new NullSpecAnalysis(checker, this, fieldValues);
  }

  @Override
  public void addDefaultAnnotations(AnnotatedTypeMirror type) {
    super.addDefaultAnnotations(type);
    /*
     * TODO(cpovirk): Find a better solution than this.
     *
     * The problem I'm working around arises during AnnotatedTypes.leastUpperBound on a
     * JSpecify-annotated variant of this code:
     * https://github.com/google/guava/blob/39aa77fa0e8912d6bfb5cb9a0bc1ed5135747b6f/guava/src/com/google/common/collect/ImmutableMultiset.java#L205
     *
     * CF is unable to infer the right type for `LinkedHashMultiset.create(elements)`: It should
     * infer `LinkedHashMultiset<? extends E>`, but instead, it infers `LinkedHashMultiset<? extends
     * Object>`. As expected, it sets isUninferredTypeArgument. As *not* expected, it gets to
     * AtmLubVisitor.lubTypeArgument with type2Wildcard.extendsBound.lowerBound (a null type)
     * missing its annotation.
     *
     * The part of CF responsible for copying annotations, including those on the extends bound, is
     * AsSuperVisitor.visitWildcard_Wildcard. Under stock CF, copyPrimaryAnnos(from, typevar) "also
     * sets primary annotations _on the bounds_." Under our CF fork, this is not the case, and we
     * end up with an unannotated lower bound on the type-variable usage E (which, again, is itself
     * a bound of a wildcard).
     *
     * (Aside: I haven't looked into how the _upper_ bound of the type-variable usage gets an
     * annotation set on it. Could it be happening "accidentally," and if so, might it be wrong
     * sometimes?)
     *
     * The result of an unannotated lower bound is a crash in NullSpecQualifierHierarchy.isSubtype,
     * which passes null to areSame.
     *
     * The workaround: If we see a type-variable usage whose lower bound is a null type that lacks
     * an annotation, we annotate that bound as non-null. This workaround shouldn't break any
     * working code, but it may or may not be universally the right solution to a missing
     * annotation.
     *
     * I am trying to ignore other questions here, such as:
     *
     * - Would it make more sense to set the lower bound to match the upper bound, as stock CF does?
     * I suspect not under our approach, but I haven't thought about it.
     *
     * - Does trying to pick correct annotations even matter in the context of an uninferred type
     * argument? Does the very idea of "correct annotations" lose meaning in that context?
     *
     * - Should we fix this in AsSuperVisitor instead? Or would it fix itself if we set bounds on
     * our type-variable usages and wildcards in the same way that stock CF does? (Following stock
     * CF would likely save us from other problems, too.)
     *
     * - What's up with the _upper_ bound, as discussed in a parenthetical above?
     */
    if (type instanceof AnnotatedTypeVariable) {
      AnnotatedTypeMirror lowerBound = ((AnnotatedTypeVariable) type).getLowerBound();
      if (lowerBound instanceof AnnotatedNullType
          && !lowerBound.isAnnotatedInHierarchy(unionNull)) {
        lowerBound.addAnnotation(minusNull);
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
    return new NullSpecAnnotatedTypeFormatter();
  }

  private final class NullSpecAnnotatedTypeFormatter implements AnnotatedTypeFormatter {
    @Override
    public String format(AnnotatedTypeMirror type) {
      return format(type, /*printVerbose=*/ false);
    }

    @Override
    public String format(AnnotatedTypeMirror type, boolean printVerbose) {
      StringBuilder result = new StringBuilder();
      Map<AnnotatedWildcardType, Present> visiting = new IdentityHashMap<>();
      new AnnotatedTypeVisitor<Void, Void>() {
        @Override
        public Void visit(AnnotatedTypeMirror type) {
          return visit(type, null);
        }

        @Override
        public Void visit(AnnotatedTypeMirror type, Void aVoid) {
          return type.accept(this, null);
        }

        @Override
        public Void visitDeclared(AnnotatedDeclaredType type, Void aVoid) {
          append(simpleName(type));
          if (!type.getTypeArguments().isEmpty()) {
            append("<");
            visitJoining(type.getTypeArguments(), ", ");
            append(">");
          }
          append(operator(type));
          return null;
        }

        @Override
        public Void visitIntersection(AnnotatedIntersectionType type, Void aVoid) {
          return visitJoining(type.getBounds(), " & ");
        }

        @Override
        public Void visitUnion(AnnotatedUnionType type, Void aVoid) {
          return visitJoining(type.getAlternatives(), " | ");
        }

        @Override
        public Void visitExecutable(AnnotatedExecutableType type, Void aVoid) {
          visit(type.getReturnType());
          append(" ");
          append(type.getElement().getSimpleName());
          append("(");
          visitJoining(type.getParameterTypes(), ", ");
          append(")");
          return null;
        }

        @Override
        public Void visitArray(AnnotatedArrayType type, Void aVoid) {
          visit(type.getComponentType());
          append("[]");
          append(operator(type));
          return null;
        }

        @Override
        public Void visitTypeVariable(AnnotatedTypeVariable type, Void aVoid) {
          append(simpleName(type));
          append(operator(type));
          return null;
        }

        @Override
        public Void visitPrimitive(AnnotatedPrimitiveType type, Void aVoid) {
          append(type.getPrimitiveKind().toString().toLowerCase(Locale.ROOT));
          return null;
        }

        @Override
        public Void visitNoType(AnnotatedNoType type, Void aVoid) {
          append("void");
          return null;
        }

        @Override
        public Void visitNull(AnnotatedNullType type, Void aVoid) {
          append("null");
          append(operator(type));
          return null;
        }

        @Override
        public Void visitWildcard(AnnotatedWildcardType type, Void aVoid) {
          Present currentlyVisiting = visiting.put(type, Present.INSTANCE);
          if (currentlyVisiting == Present.INSTANCE) {
            append("...");
            return null;
          }

          String operator = operator(type);
          if (!operator.isEmpty()) {
            append("{");
          }
          append("?");
          if (hasExtendsBound(type)) {
            append(" extends ");
            visit(type.getExtendsBound());
          }
          if (hasSuperBound(type)) {
            append(" super ");
            visit(type.getSuperBound());
          }
          if (!operator.isEmpty()) {
            append("}");
          }
          append(operator);
          visiting.remove(type);
          return null;
        }

        boolean hasExtendsBound(AnnotatedWildcardType type) {
          AnnotatedTypeMirror bound = type.getExtendsBound();
          boolean isUnbounded =
              bound instanceof AnnotatedDeclaredType
                  && ((AnnotatedDeclaredType) bound)
                      .getUnderlyingType()
                      .asElement()
                      .getSimpleName()
                      .contentEquals("Object")
                  // TODO(cpovirk): Look specifically for java.lang.Object.
                  && bound.hasAnnotation(unionNull);
          return !isUnbounded;
        }

        boolean hasSuperBound(AnnotatedWildcardType type) {
          AnnotatedTypeMirror bound = type.getSuperBound();
          boolean isUnbounded =
              bound instanceof AnnotatedNullType
                  && !bound.hasAnnotation(unionNull)
                  && !bound.hasAnnotation(nullnessOperatorUnspecified);
          return !isUnbounded;
        }

        Void visitJoining(List<? extends AnnotatedTypeMirror> types, String separator) {
          boolean first = true;
          for (AnnotatedTypeMirror type : types) {
            if (!first) {
              append(separator);
            }
            first = false;
            visit(type);
          }
          return null;
        }

        String operator(AnnotatedTypeMirror type) {
          return type.hasAnnotation(unionNull)
              ? "?"
              : type.hasAnnotation(nullnessOperatorUnspecified) ? "*" : "";
        }

        Name simpleName(AnnotatedDeclaredType type) {
          return type.getUnderlyingType().asElement().getSimpleName();
        }

        Name simpleName(AnnotatedTypeVariable type) {
          return type.getUnderlyingType().asElement().getSimpleName();
        }

        void append(Object o) {
          result.append(o);
        }
      }.visit(type);
      return result.toString();
    }
  }

  @Override
  public void postProcessClassTree(ClassTree tree) {
    /*
     * To avoid writing computed annotations into bytecode (or even into the in-memory javac Element
     * objects), do not call the supermethod.
     *
     * We don't want to write computed annotations to bytecode because we don't want for checkers
     * (including this one!) to depend on those annotations. All core JSpecify nullness information
     * should be derivable from the originally written annotations.
     *
     * (We especially don't want to write @MinusNull to bytecode, since it is an implementation
     * detail of this current checker implementation.)
     *
     * "Computed annotations" includes not only annotations added from defaults but also any
     * @Inherited/@InheritedAnnotation declaration annotations copied from supertypes. We may or may
     * not even want to support inheritance (https://github.com/jspecify/jspecify/issues/155). But
     * even if we do, we wouldn't want to produce different bytecode than a stock compiler, lest
     * tools rely on it.
     *
     * Additionally, when I was letting CF write computed annotations into bytecode, I ran into an
     * type.invalid.conflicting.annos error, which I have described more in
     * https://github.com/jspecify/nullness-checker-for-checker-framework/commit/d16a0231487e239bc94145177de464b5f77c8b19
     */
  }

  private static TypeParameterElement correspondingTypeParameter(AnnotatedWildcardType type) {
    /*
     * type.getTypeVariable() is not available in all cases that we need.
     *
     * And wildcardToTypeParam, for its part, appears to work for types in source but not in
     * bytecode?
     *
     * TODO(cpovirk): Still, is wildcardToTypeParam sufficient for our purposes in getUpperBounds? I
     * added the type.getTypeVariable() fallback only in support of a feature that I've since
     * removed. Maybe we should remove the fallback until we need it.
     */
    WildcardType wildcard = (WildcardType) type.getUnderlyingType(); // javac internal type
    TypeParameterElement fromInternal = wildcardToTypeParam(wildcard);
    if (fromInternal != null) {
      return fromInternal;
    }
    TypeVariable typeVariable = type.getTypeVariable();
    /*
     * I don't know that I've seen getTypeVariable return null in the case that wildcardToTypeParam
     * _also_ returned null -- at least not when we call this method only from getUpperBounds. (If
     * we ever start to return null to getUpperBounds, then we'll need a null check in
     * getUpperBounds!) However, I did see this method return null _to the call from getUpperBounds_
     * -- but only when I had changed our code to include _another_ call to this class in
     * NullSpecTypeAnnotator.visitWildcard. But now I have removed that other call. (It was causing
     * trouble, even when I added a null check, probably because it let me change the extends bound
     * of the wildcard in Class<?> _sometimes_ but not 100% consistently, thanks to exactly this
     * null return.)
     *
     * Anyway, I'm leaving this code in a state in which it clearly expects to sometimes return null
     * but getUpperBounds in a state in which it does not check for null. If we start seeing a null
     * return here, getUpperBounds will NPE. But that's probably better than silently failing to do
     * something and then producing a more mysterious bug later.
     */
    return type.getTypeVariable() != null ? asElement(typeVariable) : null;
  }

  private void addIfNoAnnotationPresent(AnnotatedTypeMirror type, AnnotationMirror annotation) {
    if (!type.isAnnotatedInHierarchy(unionNull)) {
      type.addAnnotation(annotation);
    }
  }

  /*
   * XXX: When adding support for aliases, make sure to support them here. But consider how to
   * handle @Inherited aliases (https://github.com/jspecify/jspecify/issues/155). In particular, we
   * have already edited getDeclAnnotations to remove its inheritance logic, and we needed to do so
   * to work around another problem (though perhaps we could have found alternatives).
   */
  private boolean hasNullAwareOrEquivalent(Element elt) {
    return getDeclAnnotation(elt, DefaultNonNull.class) != null
        // For discussion of ProtoNonnullApi, see NullSpecTypeAnnotator.visitExecutable.
        || hasAnnotationInCode(elt, "ProtoNonnullApi");
  }

  /**
   * Returns whether the given element has an annotation with the given simple name. This method
   * does not consider stub files.
   */
  private static boolean hasAnnotationInCode(AnnotatedConstruct construct, String name) {
    return construct.getAnnotationMirrors().stream().anyMatch(a -> nameMatches(a, name));
  }

  @SuppressWarnings("unchecked") // safety guaranteed by API docs
  private <T extends AnnotatedTypeMirror> T withMinusNull(T type) {
    // Remove the annotation from the *root* type, but preserve other annotations.
    type = (T) type.deepCopy(/*copyAnnotations=*/ true);
    /*
     * TODO(cpovirk): In the case of a type-variable usage, I feel like we should need to *remove*
     * any existing annotation but then not *add* minusNull. (This is because of the difference
     * between type-variable usages and all other types, as discussed near the end of the giant
     * comment in isNullExclusiveUnderEveryParameterization.) However, the current code passes all
     * tests. Figure out whether that makes sense or we need more tests to show why not.
     */
    type.replaceAnnotation(minusNull);
    return type;
  }

  @SuppressWarnings("unchecked") // safety guaranteed by API docs
  private <T extends AnnotatedTypeMirror> T withUnionNull(T type) {
    // Remove the annotation from the *root* type, but preserve other annotations.
    type = (T) type.deepCopy(/*copyAnnotations=*/ true);
    type.replaceAnnotation(unionNull);
    return type;
  }

  private static TypeParameterElement asElement(TypeVariable typeVariable) {
    return (TypeParameterElement) typeVariable.asElement();
  }

  NullSpecAnnotatedTypeFactory withLeastConvenientWorld() {
    return withLeastConvenientWorld;
  }

  NullSpecAnnotatedTypeFactory withMostConvenientWorld() {
    return withMostConvenientWorld;
  }

  private enum Present {
    INSTANCE;
  }
}
