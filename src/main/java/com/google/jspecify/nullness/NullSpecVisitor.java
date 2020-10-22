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

import static com.sun.source.tree.Tree.Kind.EXTENDS_WILDCARD;
import static com.sun.source.tree.Tree.Kind.SUPER_WILDCARD;
import static com.sun.source.tree.Tree.Kind.UNBOUNDED_WILDCARD;
import static java.util.Collections.singletonList;
import static javax.lang.model.element.ElementKind.CLASS;
import static javax.lang.model.element.ElementKind.ENUM_CONSTANT;
import static javax.lang.model.type.TypeKind.DECLARED;
import static javax.tools.Diagnostic.Kind.ERROR;
import static org.checkerframework.javacutil.AnnotationUtils.areSameByName;
import static org.checkerframework.javacutil.TreeUtils.annotationsFromTree;
import static org.checkerframework.javacutil.TreeUtils.elementFromDeclaration;
import static org.checkerframework.javacutil.TreeUtils.elementFromTree;
import static org.checkerframework.javacutil.TypesUtils.isPrimitive;

import com.sun.source.tree.AnnotatedTypeTree;
import com.sun.source.tree.ArrayAccessTree;
import com.sun.source.tree.AssertTree;
import com.sun.source.tree.BlockTree;
import com.sun.source.tree.EnhancedForLoopTree;
import com.sun.source.tree.IfTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.SynchronizedTree;
import com.sun.source.tree.ThrowTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.tree.TypeParameterTree;
import com.sun.source.tree.VariableTree;
import java.util.List;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.VariableElement;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeValidator;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.common.basetype.TypeValidator;
import org.checkerframework.framework.source.DiagMessage;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedDeclaredType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.javacutil.AnnotationBuilder;

public final class NullSpecVisitor extends BaseTypeVisitor<NullSpecAnnotatedTypeFactory> {
    private final AnnotationMirror orgJspecifyNullable;
    private final AnnotationMirror orgJspecifyNullnessUnspecified;
    private final boolean checkImpl;

    public NullSpecVisitor(BaseTypeChecker checker) {
        super(checker);
        orgJspecifyNullable =
                AnnotationBuilder.fromClass(elements, org.jspecify.annotations.Nullable.class);
        orgJspecifyNullnessUnspecified =
                AnnotationBuilder.fromClass(
                        elements, org.jspecify.annotations.NullnessUnspecified.class);
        checkImpl = checker.hasOption("checkImpl");
    }

    private void ensureNonNull(Tree tree, String messageKeyPart) {
        AnnotatedTypeMirror type = atypeFactory.getAnnotatedType(tree);
        if (!atypeFactory.isNullExclusiveUnderEveryParameterization(type)) {
            // TODO(cpovirk): Put the type in the body of the message once possible
            checker.reportError(tree, "possibly.null." + messageKeyPart + ": " + type);
        }
    }

    public Void visitBlock(BlockTree node, Void p) {
        if (checkImpl) {
            return super.visitBlock(node, p);
        } else {
            // TODO(cpovirk): Should we still check any classes inside the block (e.g., anonymous)?
            return null;
        }
    }

    @Override
    protected void checkConstructorResult(
            AnnotatedExecutableType constructorType, ExecutableElement constructorElement) {
        // TODO: ensure no explicit annotations on class & constructor
    }

    @Override
    protected void commonAssignmentCheck(
            AnnotatedTypeMirror varType,
            AnnotatedTypeMirror valueType,
            Tree valueTree,
            String errorKey,
            Object... extraArgs) {
        /*
         * TODO(cpovirk): Remove this check (and this override entirely) once we integrate dataflow,
         * which should handle primitives more generally.
         */
        if (isPrimitive(valueType.getUnderlyingType())) {
            return;
        }
        super.commonAssignmentCheck(varType, valueType, valueTree, errorKey, extraArgs);
    }

    @Override
    public Void visitMemberSelect(MemberSelectTree node, Void p) {
        if (elementFromTree(node).getKind() != CLASS) {
            ensureNonNull(node.getExpression(), "member.select");
            /*
             * By contrast, if it's CLASS, the select must be on a type, like `Foo.Baz` or
             * `Foo<Bar>.Baz`. We don't need to check that the type is non-null because the code is
             * not actually dereferencing anything.
             *
             * In fact, a check that the type is non-null is currently not *safe*: The outer type
             * appears to default to NullnessUnspecified in non-null-aware code.
             *
             * Note that our defaulting of enclosing types in
             * writeDefaultsForIntrinsicallyNonNullableComponents does not help. It does not help
             * even when I retrieve the type of the entire MemberSelectTree (and then pull out the
             * outer type from that).
             *
             * The code path that we end up in appears to be looking specifically at the class
             * referenced by the MemberSelectTree, without regard to any annotations on, e.g., the
             * VariableTree that it is the type for. We end up in AnnotatedTypeFactory.fromElement.
             * Possibly that's bogus: Not every MemberSelectTree is an "expression" in the usual
             * sense. Perhaps it's our job not to call getAnnotatedType on such trees? So let's not.
             */
        }
        return super.visitMemberSelect(node, p);
    }

    @Override
    public Void visitEnhancedForLoop(EnhancedForLoopTree node, Void p) {
        ensureNonNull(node.getExpression(), "enhanced.for");
        return super.visitEnhancedForLoop(node, p);
    }

    @Override
    public Void visitArrayAccess(ArrayAccessTree node, Void p) {
        ensureNonNull(node.getExpression(), "array.access");
        return super.visitArrayAccess(node, p);
    }

    @Override
    protected void checkThrownExpression(ThrowTree node) {
        ensureNonNull(node.getExpression(), "thrown.expression");
    }

    @Override
    public Void visitSynchronized(SynchronizedTree node, Void p) {
        ensureNonNull(node.getExpression(), "synchronized");
        return super.visitSynchronized(node, p);
    }

    @Override
    public Void visitAssert(AssertTree node, Void p) {
        ensureNonNull(node.getCondition(), "assert.condition");
        if (node.getDetail() != null) {
            ensureNonNull(node.getDetail(), "assert.detail");
        }
        return super.visitAssert(node, p);
    }

    @Override
    public Void visitIf(IfTree node, Void p) {
        ensureNonNull(node.getCondition(), "if.condition");
        return super.visitIf(node, p);
    }

    // TODO: binary, unary, compoundassign, typecast, ...

    /*
     * We report some errors of the form "X should not be annotated" in isTopLevelValidType. We do
     * that because visitAnnotatedType is not invoked in many cases we might like for it to be
     * invoked. For example, it doesn't run on an annotated return type. That's because the visit*
     * methods are triggered based on javac tree structure, and the return type's annotations get
     * attached to the *method* tree.
     *
     * Still, visitTypeParameter and visitAnnotatedType are the best places I have found for at
     * least few specific checks. That's because, for those checks especially, we probably want to
     * operate on source trees, rather than on derived types. The advantages of operating on source
     * trees are:
     *
     * - If we instead want to look for annotations on a type parameter or wildcard based on the
     * derived types, we need to ask CF questions like "What is the lower/upper bound?" since that
     * is what CF translates such annotations into. That then requires us to carefully distinguish
     * between implicit upper bounds (like the upper bound of `? super Foo`) and explicit upper
     * bounds (like the upper bound of `@Nullable ? super Foo`). This is likely to be clumsy at
     * best, requiring us to effectively look at information in the source code, anyway -- if
     * sufficient information is even available, especially across compilation boundaries!
     *
     * - IIUC, the visit* methods run only on source code that is compiled by CF. By implementing
     * those methods, we ensure that we don't report problems in our dependencies. (Or might we be
     * able to avoid that by checking isDeclaration()?)
     *
     * - We might also like that the visit* methods can check specifically for the JSpecify
     * annotations. This means that people can alias annotations like CF's own @Nullable to ours,
     * and this checker won't produce errors if they're using in non-JSpecify-recognized locations.
     * (On the other hand, some users might *want* us to produce warnings in such cases so that they
     * are informed that they're stepping outside of core JSpecify semantics.)
     */

    @Override
    public Void visitTypeParameter(TypeParameterTree node, Void p) {
        checkNoNullnessAnnotations(node, annotationsFromTree(node), "type.parameter.annotated");
        return super.visitTypeParameter(node, p);
    }

    @Override
    public Void visitAnnotatedType(AnnotatedTypeTree node, Void p) {
        Kind kind = node.getUnderlyingType().getKind();
        if (kind == UNBOUNDED_WILDCARD || kind == EXTENDS_WILDCARD || kind == SUPER_WILDCARD) {
            checkNoNullnessAnnotations(node, annotationsFromTree(node), "wildcard.annotated");
        }
        return super.visitAnnotatedType(node, p);
    }

    @Override
    public Void visitVariable(VariableTree node, Void p) {
        VariableElement element = elementFromDeclaration(node);
        if (element.getKind() == ENUM_CONSTANT) {
            checkNoNullnessAnnotations(
                    node, element.getAnnotationMirrors(), "enum.constant.annotated");
        }
        return super.visitVariable(node, p);
    }

    private void checkNoNullnessAnnotations(
            Tree node, List<? extends AnnotationMirror> annotations, String messageKey) {
        for (AnnotationMirror annotation : annotations) {
            if (areSameByName(annotation, orgJspecifyNullable)
                    || areSameByName(annotation, orgJspecifyNullnessUnspecified)) {
                checker.reportError(node, messageKey);
            }
        }
    }

    @Override
    protected TypeValidator createTypeValidator() {
        return new NullSpecTypeValidator(checker, this, atypeFactory);
    }

    private static final class NullSpecTypeValidator extends BaseTypeValidator {
        NullSpecTypeValidator(
                BaseTypeChecker checker,
                BaseTypeVisitor<?> visitor,
                AnnotatedTypeFactory atypeFactory) {
            super(checker, visitor, atypeFactory);
        }

        @Override
        protected List<DiagMessage> isTopLevelValidType(
                QualifierHierarchy qualifierHierarchy, AnnotatedTypeMirror type) {
            /*
             * This method is where we report some errors of the form "X should not be annotated."
             * But note that we report some other errors of that form in NullSpecVisitor methods
             * like visitAnnotatedType.
             *
             * TODO(cpovirk): It might actually make more sense to report *all* such errors in
             * NullSpecVisitor.visit* methods, especially to ensure that we don't report errors for
             * declarations that appear in library dependencies. However, those methods make it
             * trickier to ensure that we visit *all* annotated types, as discussed in a comment on
             * visitAnnotatedType above.
             */
            if (isPrimitive(type.getUnderlyingType()) && hasNullableOrNullnessUnspecified(type)) {
                return singletonList(new DiagMessage(ERROR, "primitive.annotated"));
            }
            if (type.getKind() == DECLARED) {
                AnnotatedDeclaredType enclosingType =
                        ((AnnotatedDeclaredType) type).getEnclosingType();
                if (enclosingType != null && hasNullableOrNullnessUnspecified(enclosingType)) {
                    return singletonList(new DiagMessage(ERROR, "outer.annotated"));
                }
            }
            return super.isTopLevelValidType(qualifierHierarchy, type);
        }

        boolean hasNullableOrNullnessUnspecified(AnnotatedTypeMirror type) {
            return type.hasAnnotation(Nullable.class)
                    || type.hasAnnotation(NullnessUnspecified.class);
        }
    }
}
