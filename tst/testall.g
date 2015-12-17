LoadPackage("cvec");
d := DirectoriesPackageLibrary("cvec","tst");

HasSuffix := function(list, suffix)
  local len;
  len := Length(list);
  if Length(list) < Length(suffix) then return false; fi;
  return list{[len-Length(suffix)+1..len]} = suffix;
end;

# Load all tests in that directory
tests := DirectoryContents(d[1]);
tests := Filtered(tests, name -> HasSuffix(name, ".tst"));
Sort(tests);

# Convert tests to filenames
tests := List(tests, test -> Filename(d,test));

# Run the tests
for test in tests do
    Test(test, rec(compareFunction:="uptowhitespace"));
od;
