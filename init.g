#############################################################################
##
#A  init.g               cvec-package                         Max Neunhoeffer
##
##  Copyright (C) 2007  Max Neunhoeffer, Lehrstuhl D f. Math., RWTH Aachen
##  This file is free software, see license information at the end.
##  
##  Initialization of the cvec package
##  

if not(IsBound(IsMatrixObj)) then
    # This should have been done whilst reading the library, but
    # released GAP 4.4 does not yet have it.
    ReadPackage("cvec", "gap/matobj1.gd");
    ReadPackage("cvec", "gap/matobj2.gd");
    ReadPackage("cvec", "gap/matobj.gi");
fi;

ReadPackage("cvec", "gap/cvec.gd");
ReadPackage("cvec", "gap/cmat.gd");
ReadPackage("cvec", "gap/linalg.gd");
ReadPackage("cvec", "gap/matrix.gd");

##
##  This program is free software; you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation; version 2 of the License.
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

