# Copyright 2020 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""Recursive subset diffs between two json/dict objects."""

import json
import sys


def sdiff(actual, expected, path):
  """Performs a subset diff between two python dicts.

  Actual is said to be a subset of expected iff:
  1. Every key in Actual exists in expected, and its value is a subset
     of the value in expected.
  2. For base values (numbers, strings, etc), the values have to be equal.
  3. For lists, the two lists must be equal in length, and every element in
     actual must be a subset of the corresponding element in expected.
  4. None values in expected are allowed to have a matching default value in
     actual (e.g. "", False, 0, []).

  Args:
    actual: the subset dict.
    expected: the super set dict.
    path: a string specifying the current path in the recursive sdiff.

  Returns:
    A tuple (status: bool, path: str), where status is True if actual
    is indeed a subset of expected, or False otherwise, and path is
    the empty string if actual is a subset, or the path of an element
    where actual disagreed with expected.

    When the path looks like foo/bar it means that
    "actual[foo][bar]" is an offending element that fails to meet
    the subset criteria.
  """
  try:
    if expected is None and not actual:  # equate default values to None
      return (True, "")

    if type(actual) != type(expected):  # pylint: disable=unidiomatic-typecheck
      return (False, path)

    if isinstance(actual, list):
      if len(actual) != len(expected):
        return (False, path)

      for i in range(len(actual)):
        status, rpath = sdiff(actual[i], expected[i], "%s/%d" % (path, i))
        if not status:
          return (status, rpath)
      return (True, "")

    if isinstance(actual, dict):
      for k in actual.keys():
        status, rpath = sdiff(actual[k], expected.get(k, None),
                              "%s/%s" % (path, str(k)))
        if not status:
          return (status, rpath)
      return (True, "")

    return (actual == expected, path)
  except Exception as exp:  # pylint: disable=broad-except
    return (False, "%s EXCEPTION %s" % (path, str(exp)))


def main():
  expected_file_path = sys.argv[1]
  with open(expected_file_path) as expected_file:
    expected = json.load(expected_file)

  actual_file_path = sys.argv[2]
  with open(actual_file_path) as actual_file:
    actual = json.load(actual_file)

  status, path = sdiff(actual, expected, "")
  if not status:
    sys.exit("not subset diff! Error at path \"%s\"" % path)


if __name__ == "__main__":
  main()
