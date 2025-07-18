#############################################################################
##  
##  PackageInfo.g for the package `cvec'
##  

SetPackageInfo( rec(

PackageName := "cvec",
Subtitle := "Compact vectors over finite fields",
Version := "2.8.4",
Date := "20/06/2025", # dd/mm/yyyy format
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
    GitHubUsername := "fingolfin",
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

Status := "deposited",

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
  GAP := ">=4.12",
  NeededOtherPackages := [
    ["GAPDoc", ">= 1.2"],
    ["IO", ">= 4.1"],
    ["orb", ">= 4.2"],
  ],
  SuggestedOtherPackages := [],
  ExternalConditions := []
),

AvailabilityTest := function()
  if not IsKernelExtensionAvailable("cvec") then
    LogPackageLoadingMessage(PACKAGE_WARNING,
                            ["the kernel module is not compiled, ",
                              "the package cannot be loaded."]);
    return false;
  fi;
  return true;
end,

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
