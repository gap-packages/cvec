#############################################################################
##  
##  PackageInfo.g for the package `cvec'
##  

SetPackageInfo( rec(

PackageName := "cvec",
Subtitle := "Compact vectors over finite fields",
Version := "2.8.1",
Date := "28/03/2023", # dd/mm/yyyy format
License := "GPL-2.0-or-later",

##  Information about authors and maintainers.
Persons := [
  rec( 
    LastName      := "Neunhöffer",
    FirstNames    := "Max",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email         := "max@9hoeffer.de",
    WWWHome       := "http://www-groups.mcs.st-and.ac.uk/~neunhoef",
    PostalAddress := Concatenation( [
                       "Gustav-Freytag-Straße 40\n",
                       "50354 Hürth\n",
                       "Germany" ] ),
    #Place         := "St Andrews",
    #Institution   := "University of St Andrews"
  ),
  rec(
    LastName      := "Horn",
    FirstNames    := "Max",
    IsAuthor      := false,
    IsMaintainer  := true,
    Email         := "mhorn@rptu.de",
    WWWHome       := "https://www.quendi.de/math",
    PostalAddress := Concatenation(
                       "Fachbereich Mathematik\n",
                       "RPTU Kaiserslautern-Landau\n",
                       "Gottlieb-Daimler-Straße 48\n",
                       "67663 Kaiserslautern\n",
                       "Germany" ),
    Place         := "Kaiserslautern, Germany",
    Institution   := "RPTU Kaiserslautern-Landau"
  ),
],

##  Status information. Currently the following cases are recognized:
##    "accepted"      for successfully refereed packages
##    "deposited"     for packages for which the GAP developers agreed 
##                    to distribute them with the core GAP system
##    "dev"           for development versions of packages 
##    "other"         for all other packages
##
# Status := "accepted",
Status := "deposited",

##  You must provide the next two entries if and only if the status is 
##  "accepted" because is was successfully refereed:
# format: 'name (place)'
# CommunicatedBy := "Mike Atkinson (St. Andrews)",
#CommunicatedBy := "",
# format: mm/yyyy
# AcceptDate := "08/1999",
#AcceptDate := "",

SourceRepository := rec(
    Type := "git",
    URL := Concatenation( "https://github.com/gap-packages/", ~.PackageName ),
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome  := Concatenation( "https://gap-packages.github.io/", ~.PackageName ),
README_URL      := Concatenation( ~.PackageWWWHome, "/README.md" ),
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "/PackageInfo.g" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/", ~.PackageName, "-", ~.Version ),
ArchiveFormats := ".tar.gz .tar.bz2",

##  Here you  must provide a short abstract explaining the package content 
##  in HTML format (used on the package overview Web page) and an URL 
##  for a Webpage with more detailed information about the package
##  (not more than a few lines, less is ok):
##  Please, use '<span class="pkgname">GAP</span>' and
##  '<span class="pkgname">MyPKG</span>' for specifing package names.
##  
AbstractHTML := 
  "This package provides an implementation of compact vectors over finite\
   fields. Contrary to earlier implementations no table lookups are used\
   but only word-based processor arithmetic. This allows for bigger finite\
   fields and higher speed.",

PackageDoc := rec(
  BookName  := "cvec",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0_mj.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Compact vectors over finite fields",
),

Dependencies := rec(
  GAP := ">=4.10",
  NeededOtherPackages := [
    ["GAPDoc", ">= 1.2"],
    ["IO", ">= 4.1"],
    ["orb", ">= 4.2"],
  ],
  SuggestedOtherPackages := [],
  ExternalConditions := []
),

AvailabilityTest := function()
  if CompareVersionNumbers(GAPInfo.Version, "4.12") then
    if not IsKernelExtensionAvailable("cvec") then
      LogPackageLoadingMessage(PACKAGE_WARNING,
                              ["the kernel module is not compiled, ",
                               "the package cannot be loaded."]);
      return fail;
    fi;
  else
    # TODO this clause can be removed once cvec requires GAP>=4.12.1
    digraphs_so := Filename(DirectoriesPackagePrograms("digraphs"),
                            "digraphs.so");
    if not "cvec" in SHOW_STAT() and
       Filename(DirectoriesPackagePrograms("cvec"), "cvec.so") = fail then
       LogPackageLoadingMessage(PACKAGE_WARNING,
                                ["the kernel module is not compiled, ",
                                 "the package cannot be loaded."]);
      return fail;
    fi;
  return true;
end,

##  *Optional*, but recommended: path relative to package root to a file which 
##  contains as many tests of the package functionality as sensible.
TestFile := "tst/testall.g",

##  *Optional*: Here you can list some keyword related to the topic 
##  of the package.
Keywords := [],

AutoDoc := rec(
    TitlePage := rec(
    Copyright := """
      &copyright; 2005-2014 by Max Neunhöffer<P/>

      <Package>cvec</Package> is free software: you can redistribute it and/or modify
      it under the terms of the GNU General Public License as published by
      the Free Software Foundation, either version 2 of the License, or
      (at your option) any later version. <P/>

      <Package>cvec</Package> is distributed in the hope that it will be useful,
      but WITHOUT ANY WARRANTY; without even the implied warranty of
      MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
      GNU General Public License for more details. <P/>

      For a copy of the GNU General Public License, see
      the file <F>LICENSE</F> included with this software,
      or see <URL>https://www.gnu.org/licenses/gpl.html</URL>.
      """,
    )
),

));


