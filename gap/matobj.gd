############################################################################
# 
# matobj.gd
#                                                        by Max Neunhoeffer
#
# Copyright (C) 2006 by Lehrstuhl D fuer Mathematik, RWTH Aachen
#
# This file formally defines the interface to the new style vectors
# and matrices in GAP.
#
############################################################################


############################################################################
# Overview:
#
# The whole idea of this interface is that vectors and matrices must
# be proper objects with a stored type (i.e. created by Objectify allowing
# inheritance) to benefit from method selection. This is not true for
# lists of lists which have traditionally been matrices in GAP and whose
# type is computed rather expensively on the fly every time the method
# selections considers them. In addition it should be possible to write
# (efficient) code that is independent of the actual representation (in
# the sense of GAP's representation filters) and preserves it.
#
# This latter requirement makes it necessary to distinguish between
# (at least) two classes of matrices:
#   (1) "RowList"-Matrices which behave basically like lists of rows,
#       in particular are the rows individual GAP objects that can
#       be shared between different matrix objects.
#   (2) "Flat" matrices which behave basically like one GAP object
#       that cannot be split up further. In particular a row is only
#       a part of a matrix and no GAP object in itself.
# For various reasons these two classes have to be distinguished
# already with respect to the definition of the operations for them.
#
# Every representation of matrices has a corresponding vector
# representation. The same vector representation can be used for
# more than one matrix representation.
#
# In particular vectors and matrices know their BaseDomain and their
# dimensions. Note that the basic condition is that the elements of
# vectors and matrices must either lie in the BaseDomain or naturally
# embed in the sense that + and * and = automatically work with all elements
# of the base domain (example: integers in polynomials over integers).
#
# Vectors are equal with respect to "=" if they have the same length
# and the same entries. It is not necessary that they have the same
# BaseDomain. Matrices are equal with respect to "=" if they have the
# same dimensions and the same entries. It is possible that not for all
# pairs of representations methods exist.
#
# The way to write code that preserves the representation basically
# works by using constructor operations that take template objects
# to decide about the actual representation of the new object.
#
# Vectors do not have to be lists in the sense that they do not have
# to support all list operations. The same holds for matrices. However,
# RowList matrices behave nearly like lists of row vectors that insist
# on being dense and containing only vectors of the same length and
# with the same BaseDomain.
#
# There are some rules embedded in the comments to the following code.
# They are marked with the word "Rule".
############################################################################


############################################################################
# If some operation has no comment it behaves as expected from
# the old vectors/matrices or as defined elsewhere.
############################################################################


############################################################################
############################################################################
# Categories for vectors and matrices:
############################################################################
############################################################################


DeclareCategory( "IsRowVectorObj", IsVector and IsCopyable );
# All the arithmetical filters come from IsVector.
# RowVectors are no longer necessarily lists, since they do not promise all 
# list operations. Of course, in specific implementations the objects
# may still be lists.
# The family of an object in IsRowVectorObj is the same as the family of
# the base domain.

# There are one main category for matrices and two disjoint sub-categories:

DeclareCategory( "IsMatrixObj", IsVector and IsScalar and IsCopyable );
# All the arithmetical filters come from IsVector and IsRingElement.
# In particular, matrices are in "IsMultiplicativeElement" which defines
# powering with a positive integer by the (kernel) method for POW_OBJ_INT.
# Note that this is at least strange for non-associative base domains.
# Matrices are no longer necessarily lists, since they do not promise all list
# operations! Of course, in specific implementations the objects may
# still be lists.
# The family of an object in IsMatrixObj is the collections family of
# the family of its base domain.

DeclareCategory( "IsRowListMatrix", IsMatrixObj );
# The category of matrices behaving like lists of rows which are GAP objects.
# Different matrices in this category can share rows and the same row can
# occur more than once in a matrix. Row access just gives a reference
# to the row object.

DeclareCategory( "IsFlatMatrix", IsMatrixObj );
# The category of "flatly" stored matrices. They behave as if all their rows
# were in one single chunk of memory, such that rows are not individual
# GAP objects. Writing row access and slicing always copies.
# Note that read-accessing the i-th row of a flat matrix twice can
# yield two non-identical objects!


############################################################################
############################################################################
# Attributes for vectors:
############################################################################
############################################################################


############################################################################
# Rule:
# A base domain must be a GAP object that has at least the following
# methods implemented:
#  Zero
#  One
#  \in
#  Characteristic
#  IsFinite
#     if finite:  Size, and possibly DegreeFFE for fields
# Elements of the base domain must implement + and *.
# "Automatically" embedded elements may occur in vectors and matrices.
# Example: An integer i may occur in a matrix with BaseDomain a polynomial
#          ring over the Rationals.
############################################################################


# The following are guaranteed to be always set or cheaply calculable:
DeclareAttribute( "BaseDomain", IsRowVectorObj );
# Typically, the base domain will be a ring, it need not be commutative
# nor associative. For non-associative base domains powering of matrices
# is defined to be A^3 = (A*A)*A .

DeclareAttribute( "Length", IsRowVectorObj );    # can be zero

############################################################################
# Rule:
# Vectors v are always dense in the sense that all entries in the
# range [1..Length(v)] have defined values from BaseDomain(v).
############################################################################


############################################################################
############################################################################
# Operations for vectors:
############################################################################
############################################################################


############################################################################
# Rule:
# Vectors may be mutable or immutable. Of course all operations changing
# a vector are only allowed/implemented for mutable vectors.
############################################################################


############################################################################
# In the following sense vectors behave like lists:
############################################################################

DeclareOperation( "[]", [IsRowVectorObj,IsPosInt] );
# This is only defined for positions in [1..Length(VECTOR)]. 

DeclareOperation( "[]:=", [IsRowVectorObj,IsPosInt,IsObject] );
# This is only guaranteed to work for the position in [1..Length(VECTOR)] 
# and only for elements in the BaseDomain(VECTOR)! 
# Behaviour otherwise is undefined (from "unpacking" to Error all is possible)

DeclareOperation( "{}", [IsRowVectorObj,IsList] );
# Of course the positions must all lie in [1..Length(VECTOR)].
# Returns a vector in the same representation!

DeclareOperation( "PositionNonZero", [IsRowVectorObj] );

DeclareOperation( "PositionLastNonZero", [IsRowVectorObj] );

DeclareOperation( "ListOp", [IsRowVectorObj] );
DeclareOperation( "ListOp", [IsRowVectorObj,IsFunction] );
# This is an unpacking operation returning a mutable copy in form of a list.
# It enables the "List" function to work.

# I intentionally left out "PositionNot" here because it can rarely
# be implemented much more efficiently than by running through the vector.

# Note that vectors need not behave like lists with respect to the 
# following operations:
#  Add, Remove, IsBound[], Unbind[], \{\}\:\=, Append, Concatenation,
#  Position, First, Filtered, ...
# Note that \{\}\:\= is left out here since it tempts the programmer
# to use constructions like A{[1..3]} := B{[4,5,6]} which produces
# an intermediate object. Use CopySubVector instead!
# The list operations Position and so on seem to be unnecessary for
# vectors and matrices and thus are left out to simplify the interface.


############################################################################
# Standard operations for all objects:
############################################################################

# The following are implicitly there for all objects, we mention them here
# to have a complete interface description in one place. Of course, vectors
# have to implement those:

# DeclareOperation( "ShallowCopy", [IsRowVectorObj] );

# DeclareGlobalFunction( "StructuralCopy", [IsRowVectorObj] );

# DeclareOperation( "ViewObj", [IsRowVectorObj] );

# DeclareOperation( "PrintObj", [IsRowVectorObj] );
# This must produce GAP readable input reproducing the representation!

# DeclareAttribute( "String", IsRowVectorObj );
# DeclareOperation( "String", [IsRowVectorObj,IsInt] );

# DeclareOperation( "Display", [IsRowVectorObj] );

# DeclareOperation( "MakeImmutable", [IsRowVectorObj] );
#  (this is a global function in the GAP library)


############################################################################
# Arithmetical operations for vectors:
############################################################################

# The following binary arithmetical operations are possible for vectors
# over the same BaseDomain with equal length:
#    +, -, <, =
# Note: It is not guaranteed that sorting is done lexicographically!

# The following "in place" operations exist with the same restrictions:
DeclareOperation( "AddRowVector", 
  [ IsRowVectorObj and IsMutable, IsRowVectorObj ] );
DeclareOperation( "AddRowVector", 
  [ IsRowVectorObj and IsMutable, IsRowVectorObj, IsObject ] );
DeclareOperation( "AddRowVector", 
  [ IsRowVectorObj and IsMutable,IsRowVectorObj,IsObject,IsPosInt,IsPosInt ] );
DeclareOperation( "MultRowVector",
  [ IsRowVectorObj and IsMutable, IsObject ] );
DeclareOperation( "MultRowVector",
  [ IsRowVectorObj and IsMutable, IsList, IsRowVectorObj, IsList, IsObject ] );

# The following operations for scalars and vectors are possible of course
# only for scalars in the BaseDomain:
#    *, /

# The following unary arithmetical operations are possible for vectors:
#    AdditiveInverseImmutable, AdditiveInverseMutable, 
#    AdditiveInverseSameMutability, ZeroImmutable, ZeroMutable, 
#    ZeroSameMutability, IsZero, Characteristic


############################################################################
# The "representation-preserving" contructor methods:
############################################################################

DeclareOperation( "ZeroVector", [IsInt,IsRowVectorObj] );
# Returns a new mutable zero vector in the same rep as the given one with
# a possible different length.

DeclareOperation( "Vector", [IsList,IsRowVectorObj]);
# Creates a new vector in the same representation but with entries from list.
# The length is given by the length of the list.


############################################################################
# Some things that fit nowhere else:
############################################################################

DeclareOperation( "Randomize", [IsRowVectorObj] );
# Changes the mutable argument in place, every entry is replaced
# by a random element from BaseDomain.

# Already in the library:
# DeclareOperation( "CopySubVector", [IsRowVectorObj,IsRowVectorObj,
#                                     IsList,IsList] );
# CopySubVector(a,b,src,dst) does b{dst} := a{src} efficiently without
# generating an intermediate object.



############################################################################
############################################################################
# Operations for all matrices in IsMatrixObj:
############################################################################
############################################################################


############################################################################
# Attributes of matrices:
############################################################################

# The following are guaranteed to be always set or cheaply calculable:
DeclareAttribute( "BaseDomain", IsMatrixObj );
# Typically, the base domain will be a ring, it need not be commutative
# nor associative. For non-associative base domains powering of matrices
# is defined to be A^3 = (A*A)*A .

DeclareAttribute( "Length", IsMatrixObj );

DeclareAttribute( "RowLength", IsMatrixObj );

DeclareAttribute( "Dimensions", IsMatrixObj );   # returns [rows,cols]


############################################################################
# In the following sense matrices behave like lists:
############################################################################

DeclareOperation( "[]", [IsMatrixObj,IsPosInt] );
# This is guaranteed to return a vector object that has the property
# that changing it changes the matrix!
# A flat matrix has to create an intermediate object that refers to some
# row within it to allow the old GAP syntax M[i][j] for read and write
# access to work. Note that this will never be particularly efficient
# for flat matrices. Efficient code will have to use ElmMatrix and
# AssMatrix instead.

DeclareOperation( "PositionNonZero", [IsMatrixObj] );
DeclareOperation( "PositionNonZero", [IsMatrixObj, IsInt] );

DeclareOperation( "PositionLastNonZero", [IsMatrixObj] );
DeclareOperation( "PositionLastNonZero", [IsMatrixObj, IsInt] );

DeclareOperation( "Position", [IsMatrixObj, IsRowVectorObj] );
DeclareOperation( "Position", [IsMatrixObj, IsRowVectorObj, IsInt] );

DeclareOperation( "PositionSorted", [IsMatrixObj, IsRowVectorObj] );
DeclareOperation( "PositionSorted", [IsMatrixObj, IsRowVectorObj, IsFunction] );

# I intentionally left out "PositionNot" here.

# Note that "PositionSet" is a function only for lists. End of story.

# Note that arbitrary matrices need not behave like lists with respect to the 
# following operations:
#  Add, Remove, IsBound, Unbind, \{\}\:\=, Append, Concatenation,
# However, see below for matrices in the subcategory IsRowListMatrix.


############################################################################
# Explicit copying operations:
############################################################################

# The following are already in the library:
#DeclareOperation( "CopySubMatrix", [IsMatrixObj,IsMatrixObj,
#                                    IsList,IsList,IsList,IsList] );
#DeclareOperation( "ExtractSubMatrix", [IsMatrixObj,IsList,IsList] );
DeclareOperation( "MutableCopyMat", [IsMatrixObj] );


############################################################################
# New element access for matrices (especially necessary for flat mats:
############################################################################

DeclareOperation( "ElmMatrix", [IsMatrixObj,IsPosInt,IsPosInt] );

DeclareOperation( "AssMatrix", [IsMatrixObj,IsPosInt,IsPosInt,IsObject] );


############################################################################
# Standard operations for all objects:
############################################################################

# The following are implicitly there for all objects, we mention them here
# to have a complete interface description in one place:

# ShallowCopy is missing here since its behaviour depends on the matrix
# being in IsRowListMatrix or in IsFlatMatrix!

# DeclareGlobalFunction( "StructuralCopy", [IsMatrixObj] );

# DeclareOperation( "ViewObj", [IsMatrixObj] );

# DeclareOperation( "PrintObj", [IsMatrixObj] );
# This must produce GAP-readable input reproducing the representation.

# DeclareAttribute( "String", IsMatrixObj );
# DeclareOperation( "String", [IsMatrixObj,IsInt] );

# DeclareOperation( "Display", [IsMatrixObj] );

# DeclareOperation( "MakeImmutable", [IsMatrixObj] );
#  (this is a global function in the GAP library)
# Matrices have to implement "PostMakeImmutable" if necessary!


############################################################################
# Arithmetical operations:
############################################################################

# The following binary arithmetical operations are possible for matrices
# over the same BaseDomain with fitting dimensions:
#    +, *, -
# The following are also allowed for different dimensions:
#    <, =
# Note: It is not guaranteed that sorting is done lexicographically!
# Note2: If sorting is not done lexicographically then the objects
#        in that representation cannot be lists!

# For non-empty square matrices we have:
#    ^ integer

# The following unary arithmetical operations are possible for matrices:
#    AdditiveInverseImmutable, AdditiveInverseMutable, 
#    AdditiveInverseSameMutability, ZeroImmutable, ZeroMutable, 
#    ZeroSameMutability, IsZero, Characteristic

# The following unary arithmetical operations are possible for non-empty
# square matrices (inversion returns fail if not invertible):
#    OneMutable, OneImmutable, OneSameMutability,
#    InverseMutable, InverseImmutable, InverseSameMutability, IsOne,

# Problem: How about inverses of integer matrices that exist as
# elements of rationals matrix?


############################################################################
# Rule:
# Operations not sensibly defined return fail and do not trigger an error:
# In particular this holds for:
# One for non-square matrices.
# Inverse for non-square matrices
# Inverse for square, non-invertible matrices.
# Powering for non-square matrices.
# IsOne for non-square matrices.
############################################################################

############################################################################
# The "representation-preserving" contructor methods:
############################################################################

DeclareOperation( "ZeroMatrix", [IsInt,IsInt,IsMatrixObj] );
# Returns a new mutable zero matrix in the same rep as the given one with
# possibly different dimensions.

DeclareOperation( "IdentityMatrix", [IsInt,IsMatrixObj] );
# Returns a new mutable identity matrix in the same rep as the given one with
# possibly different dimensions.

# The following are already declared in the library:
# Eventually here will be the right place to do this.

# DeclareOperation( "Matrix", [IsList,IsMatrixObj]);
# Creates a new matrix in the same representation but with entries from list,
# which must be a list of vectors or a list of lists of values.


############################################################################
# Some things that fit nowhere else:
############################################################################

DeclareOperation( "Randomize", [IsMatrixObj] );
# Changes the mutable argument in place, every entry is replaced
# by a random element from BaseDomain.

DeclareAttribute( "TransposedMatImmutable", IsMatrixObj );
DeclareOperation( "TransposedMatMutable", [IsMatrixObj] );

DeclareOperation( "IsDiagonalMatrix", [IsMatrixObj] );

DeclareOperation( "IsUpperTriangularMatrix", [IsMatrixObj] );
DeclareOperation( "IsLowerTriangularMatrix", [IsMatrixObj] );

DeclareOperation( "KroneckerProduct", [IsMatrixObj,IsMatrixObj] );
# The result is fully mutable.


############################################################################
############################################################################
# Operations for RowList-matrices:
############################################################################
############################################################################


############################################################################
# List operations with some restrictions:
############################################################################

DeclareOperation( "[]:=", [IsRowListMatrix,IsPosInt,IsObject] );
# Only guaranteed to work for the position in [1..Length(VECTOR)] and only
# for elements in the corresponding vector type.
# Behaviour otherwise is undefined (from "unpacking" to Error all is possible)

DeclareOperation( "{}", [IsRowListMatrix,IsList] );
# Produces *not* a list of rows but a matrix in the same rep as the input!

DeclareOperation( "Add", [IsRowListMatrix,IsRowVectorObj] );
DeclareOperation( "Add", [IsRowListMatrix,IsRowVectorObj,IsPosInt] );

DeclareOperation( "Remove", [IsRowListMatrix] );
DeclareOperation( "Remove", [IsRowListMatrix,IsPosInt] );

DeclareOperation( "IsBound[]", [IsRowListMatrix,IsPosInt] );
DeclareOperation( "Unbind[]", [IsRowListMatrix,IsPosInt] );  
# Only works for last row to preserve denseness.

DeclareOperation( "{}:=", [IsRowListMatrix,IsList,IsRowListMatrix] );
# This is only guaranteed to work if the result is dense and the matrices
# are compatible. For efficiency reasons the third argument must be a
# matrix and cannot be a list of vectors.

DeclareOperation( "Append", [IsRowListMatrix,IsRowListMatrix] ); 
# Again only for compatible matrices
# ==> Concatenation works then automatically!

# Implicitly there, creates a new matrix sharing the same rows:
# DeclareOperation( "ShallowCopy", [IsRowListMatrix] );

# The following unwraps a matrix to a list of vectors:
DeclareOperation( "ListOp", [IsRowListMatrix] );
DeclareOperation( "ListOp", [IsRowListMatrix, IsFunction] );

# The following unwraps a matrix to a list of lists:
DeclareOperation( "Unpack", [IsRowListMatrix] );


############################################################################
# Rule:
# This all means that objects in IsRowListMatrix behave like lists that
# insist on being dense and having only IsRowVectorObjs over the right
# BaseDomain and with the right length as entries. However, formally
# they do not have to lie in the filter IsList.
############################################################################


############################################################################
############################################################################
# Operations for flat matrices:
############################################################################
############################################################################


############################################################################
# List operations with some modifications:
############################################################################

DeclareOperation( "[]:=", [IsFlatMatrix,IsPosInt,IsObject] );
# Only guaranteed to work for the position in [1..Length(VECTOR)] and only
# for elements in the corresponding vector type.
# Here this is always a copying operation!
# Behaviour otherwise is undefined (from "unpacking" to Error all is possible)

DeclareOperation( "{}", [IsFlatMatrix,IsList] );
# Again this is defined to be a copying operation!

# The following list operations are not supported for flat matrices:
# Add, Remove, IsBound[], Unbind[], {}:=, Append

# ShallowCopy is in fact a structural copy here:
# DeclareOperation( "ShallowCopy", [IsFlatMatrix] );


############################################################################
# Rule:
# Objects in IsFlatMatrix are not lists and do not behave like them.
############################################################################


############################################################################
# Arithmetic involving vectors and matrices:
############################################################################

# DeclareOperation( "*", [IsRowVectorObj, IsMatrixObj] );

# DeclareOperation( "^", [IsRowVectorObj, IsMatrixObj] );

# Only in this direction since vectors are row vectors. The standard
# list arithmetic rules apply only in this sense here which is the
# standard mathematical vector matrix multiplication.


############################################################################
# Rule:
# Note that vectors are by convention row vectors.
############################################################################


############################################################################
# Further candidates for the interface:
############################################################################

# AsList
# AddCoeffs

# Throw-out candidates: VectorNC and MatrixNC
