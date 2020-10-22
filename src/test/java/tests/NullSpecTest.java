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

import com.google.jspecify.nullness.NullSpecChecker;
import java.io.File;
import java.util.List;
import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest;
import org.junit.runners.Parameterized.Parameters;

public class NullSpecTest extends CheckerFrameworkPerDirectoryTest {
  public NullSpecTest(List<File> testFiles) {
    super(testFiles, NullSpecChecker.class, "NullSpec", "-Anomsgtext", "-Astubs=stubs/", "-nowarn");
  }

  @Parameters
  public static String[] getTestDirs() {
    return new String[] {"nullspec-common"};
  }
}
