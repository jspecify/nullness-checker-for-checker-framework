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

package tests;

import com.google.jspecify.nullness.NullSpecChecker;
import java.io.File;
import java.util.ArrayList;
import java.util.List;
import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest;
import org.checkerframework.framework.test.TypecheckResult;
import org.checkerframework.framework.test.diagnostics.DiagnosticKind;
import org.checkerframework.framework.test.diagnostics.TestDiagnostic;
import org.checkerframework.javacutil.BugInCF;
import org.junit.runners.Parameterized.Parameters;

public class NullSpecTest {
  public static class Lenient extends CheckerFrameworkPerDirectoryTest {
    public Lenient(List<File> testFiles) {
      super(
          testFiles,
          NullSpecChecker.class,
          "NullSpec",
          "-nowarn",
          "-Anomsgtext",
          "-Astubs=stubs/",
          "-AcheckImpl",
          "-AsuppressWarnings=conditional.type.incompatible");
    }

    @Parameters
    public static String[] getTestDirs() {
      return new String[] {"../../jspecify/samples"};
    }

    @Override
    public TypecheckResult adjustTypecheckResult(TypecheckResult testResult) {
      return NullSpecTest.adjustTypecheckResult(testResult, false);
    }
  }

  public static class Strict extends CheckerFrameworkPerDirectoryTest {
    public Strict(List<File> testFiles) {
      super(
          testFiles,
          NullSpecChecker.class,
          "NullSpec",
          "-nowarn",
          "-Anomsgtext",
          "-Astubs=stubs/",
          "-AcheckImpl",
          "-AsuppressWarnings=conditional.type.incompatible",
          "-Astrict");
    }

    @Parameters
    public static String[] getTestDirs() {
      return new String[] {"../../jspecify/samples"};
    }

    @Override
    public TypecheckResult adjustTypecheckResult(TypecheckResult testResult) {
      return NullSpecTest.adjustTypecheckResult(testResult, true);
    }
  }

  protected static TypecheckResult adjustTypecheckResult(
      TypecheckResult testResult, boolean strict) {
    // Aliases to lists in testResult - side-effecting the returned value.
    List<TestDiagnostic> missing = testResult.getMissingDiagnostics();
    List<TestDiagnostic> unexpected = testResult.getUnexpectedDiagnostics();

    // The original values to allow multiple complete iterations - multiple unexpected errors
    // can be mapped to a single missing error.
    List<TestDiagnostic> origMissing = new ArrayList<>(missing);
    List<TestDiagnostic> origUnexpected = new ArrayList<>(unexpected);

    for (TestDiagnostic m : origMissing) {
      unexpected.removeIf(u -> corresponds(m, u, strict));
    }
    for (TestDiagnostic u : origUnexpected) {
      missing.removeIf(m -> corresponds(m, u, strict));
    }
    if (!strict) {
      // Filter out all errors do to limited information
      missing.removeIf(m -> m.getMessage().equals("jspecify_nullness_not_enough_information"));
    }
    // TODO: should only errors matter? Only in strict mode?
    unexpected.removeIf(u -> u.getKind() != DiagnosticKind.Error);

    return testResult;
  }

  protected static boolean corresponds(
      TestDiagnostic missing, TestDiagnostic unexpected, boolean strict) {
    // First, make sure the two diagnostics are on the same file and line.
    if (!missing.getFilename().equals(unexpected.getFilename())
        || missing.getLineNumber() != unexpected.getLineNumber()) {
      return false;
    }

    switch (missing.getMessage()) {
      case "jspecify_nullness_not_enough_information":
        if (!strict) {
          return true;
        }
        // fall through
      case "jspecify_nullness_mismatch":
        switch (unexpected.getMessage()) {
          case "argument.type.incompatible":
          case "assignment.type.incompatible":
          case "cast.unsafe":
          case "dereference":
          case "override.param.invalid":
          case "override.return.invalid":
          case "return.type.incompatible":
          case "type.argument.type.incompatible":
            return true;
          default:
            return false;
        }
      case "jspecify_nullness_intrinsically_not_nullable":
        switch (unexpected.getMessage()) {
          case "enum.constant.annotated":
          case "outer.annotated":
          case "primitive.annotated":
            return true;
          default:
            return false;
        }
      case "jspecify_unrecognized_location":
        switch (unexpected.getMessage()) {
          case "type.parameter.annotated":
          case "wildcard.annotated":
            return true;
          default:
            return false;
        }
      case "jspecify_conflicting_annotations":
        switch (unexpected.getMessage()) {
          case "type.invalid.conflicting.annos":
            return true;
          default:
            return false;
        }
      default:
        throw new BugInCF("Unexpected missing diagnostic: " + missing.getMessage());
    }
  }
}
