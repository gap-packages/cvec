gap> START_TEST("cvec: builtin/slice.tst");

#
gap> CVEC.TEST.LIMIT_ALLFFE:=32;;
gap> CVEC.TEST.LIMIT_SLICE:=32;;
gap> inf := InfoLevel(InfoWarning);;
gap> SetInfoLevel(InfoWarning,0);;  # Get rid of messages for Conway polynomials

#
gap> CVEC.TEST.SLICE(2,1);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICE(3,1);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICE(5,1);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICE(11,1);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICE(19,1);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICE(37,1);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICE(101,1);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICE(2,2);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICE(3,2);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICE(5,2);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICE(2,3);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICE(3,3);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICE(2,4);
srcpos=1 (32)
srcpos=2 (32)
srcpos=3 (32)
srcpos=4 (32)
srcpos=5 (32)
srcpos=6 (32)
srcpos=7 (32)
srcpos=8 (32)
srcpos=9 (32)
srcpos=10 (32)
srcpos=11 (32)
srcpos=12 (32)
srcpos=13 (32)
srcpos=14 (32)
srcpos=15 (32)
srcpos=16 (32)
srcpos=17 (32)
srcpos=18 (32)
srcpos=19 (32)
srcpos=20 (32)
srcpos=21 (32)
srcpos=22 (32)
srcpos=23 (32)
srcpos=24 (32)
srcpos=25 (32)
srcpos=26 (32)
srcpos=27 (32)
srcpos=28 (32)
srcpos=29 (32)
srcpos=30 (32)
srcpos=31 (32)
srcpos=32 (32)

#
gap> CVEC.TEST.SLICELIST(2,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.SLICELIST(3,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.SLICELIST(5,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.SLICELIST(11,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.SLICELIST(19,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.SLICELIST(37,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.SLICELIST(101,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.SLICELIST(2,2);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.SLICELIST(3,2);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.SLICELIST(5,2);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.SLICELIST(2,3);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.SLICELIST(3,3);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.SLICELIST(2,4);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(2,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(3,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(5,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(11,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(19,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(37,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(101,1);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(2,2);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(3,2);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(5,2);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(2,3);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(3,3);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> CVEC.TEST.COPYSUBMATRIX(2,4);
Testing lists for srcposs and dstposs...
Testing list for srcposs and range for dstposs...
Testing list for dstposs and range for srcposs...
Testing ranges for srcposs and dstposs...

#
gap> SetInfoLevel(InfoWarning,inf);
gap> STOP_TEST("cvec: builtin/slice.tst", 1);
