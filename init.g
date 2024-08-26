#############################################################################
##
#A  init.g               cvec-package                         Max Neunhoeffer
##
##  Copyright (C) 2007  Max Neunhoeffer, Lehrstuhl D f. Math., RWTH Aachen
##  This file is free software, see license information at the end.
##  
##  Initialization of the cvec package
##  

################################
# First look after our C part: #
################################

# load kernel function if it is installed:
if CompareVersionNumbers(GAPInfo.Version, "4.12") then
  if not LoadKernelExtension("cvec") then
    Error("failed to load the cvec package kernel extension");
  fi;
else
  # TODO this clause can be removed once cvec requires GAP>=4.12.1
  # load kernel function if it is installed:
  if (not IsBound(CVEC)) and ("cvec" in SHOW_STAT()) then
    # try static module
    LoadStaticModule("cvec");
  fi;
  if (not IsBound(CVEC)) and
    (Filename(DirectoriesPackagePrograms("cvec"), "cvec.so") <> fail) then
    LoadDynamicModule(Filename(DirectoriesPackagePrograms("cvec"), "cvec.so"));
  fi;
fi;

#
# Compatibility between older and newer versions of the MatrixObj interface
#
if not IsBound(MultVector) then
    DeclareSynonym( "MultVector", MultRowVector );
fi;
if not IsBound(NumberColumns) then
    DeclareSynonymAttr( "NumberColumns", RowLength );
    DeclareSynonymAttr( "NumberRows", Length );
fi;

ReadPackage("cvec", "gap/cvec.gd");
ReadPackage("cvec", "gap/cmat.gd");
ReadPackage("cvec", "gap/linalg.gd");

##
##  This program is free software; you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation; either version 2 of the License,
##  or (at your option) any later version.
##
##  This program is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  You should have received a copy of the GNU General Public License
##  along with this program; if not, write to the Free Software
##  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
##

