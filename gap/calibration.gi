#############################################################################
##
##  greasecalibration.gi           GAP 4 package `cvec'                
##                                                            Max Neunhoeffer
##
##  Copyright (C) 2007  Max Neunhoeffer, Lehrstuhl D f. Math., RWTH Aachen
##  This file is free software, see license information at the end.
##
##  This file contains grease calibration data.
##
#############################################################################

# This data was obtained on host algol in LDfM.

CVEC_CalibrationTableCache := [,
# q=2:
[2,2,4,16,48,128,320,768],
# q=3:
[4,4,27,135,567,2187,8019,28431],
# q=4:
[2,8,80,512,2816,14336,69632,327680],
# q=5:
[1,15,175,1375,9375,59375,359375],,
# q=7:
[3,35,539,5831,55223,487403],
# q=8:
[1,48,832,10240,110592],
# q=9:
[2,63,1215,16767,203391],,
# q=11:
[2,99,2299,38599,570999],,
# q=13:
[3,143,3887,76895],,,
# q=16:
[2,224,7424,180224],
# q=17:
[2,255,8959,230911],,
# q=19:
[3,323,12635,363527],,,,
# q=23:
[3,483,22747,790855],,
# q=25:
[3,575,29375],,
# q=27:
[2,675,37179],,
# q=29:
[5,783,46255],,
# q=31:
[6,899,56699],
# q=32:
[2,960,62464],,,,,
# q=37:
[5,1295,97199],,,,
# q=41:
[5,1599,132799],,
# q=43:
[6,1763,153467],,,,
# q=47:
[11,2115,201019],,
# q=49:
[4,2303,228095],,,,
# q=53:
[7,2703,289327],,,,,,
# q=59:
[8,3363,400315],,
# q=61:
[6,3599,442799],,,
# q=64:
[2,3968,512000],,,
# q=67:
[7,4355,588059],,,,
# q=71:
[8,4899,700699],,
# q=73:
[8,5183,762047],,,,,,
# q=79:
[9,6083,967355],,
# q=81:
[4,6399],,
# q=83:
[8,6723],,,,,,
# q=89:
[11,7743],,,,,,,,
# q=97:
[9,9215],,,,
# q=101:
[11,9999],,
# q=103:
[9,10403],,,,
# q=107:
[11,11235],,
# q=109:
[12,11663],,,,
# q=113:
[12,12543],,,,,,,,
# q=121:
[8,14399],,,,
# q=125:
[8,15375],,
# q=127:
[12,15875],
# q=128:
[3,16128],,,
# q=131:
[14,16899],,,,,,
# q=137:
[17,18495],,
# q=139:
[6,19043],,,,,,,,,,
# q=149:
[14,21903],,
# q=151:
[13,22499],,,,,,
# q=157:
[14,24335],,,,,,
# q=163:
[16,26243],,,,
# q=167:
[16,27555],,
# q=169:
[14,28223],,,,
# q=173:
[14,29583],,,,,,
# q=179:
[16,31683],,
# q=181:
[16,32399],,,,,,,,,,
# q=191:
[15,36099],,
# q=193:
[14,36863],,,,
# q=197:
[16,38415],,
# q=199:
[16,39203],,,,,,,,,,,,
# q=211:
[21,44099],,,,,,,,,,,,
# q=223:
[22,49283],,,,
# q=227:
[22,51075],,
# q=229:
[22,51983],,,,
# q=233:
[23,53823],,,,,,
# q=239:
[23,56643],,
# q=241:
[21,57599],,
# q=243:
[11,58563],,,,,,,,
# q=251:
[22,62499],,,,,
# q=256:
[6,65024],
# q=257:
[19,65535],,,,,,
# q=263:
[18,68643],,,,,,
# q=269:
[19,71823],,
# q=271:
[19,72899],,,,,,
# q=277:
[21,76175],,,,
# q=281:
[25,78399],,
# q=283:
[25,79523],,,,,,
# q=289:
[20,82943],,,,
# q=293:
[22,85263],,,,,,,,,,,,,,
# q=307:
[21,93635],,,,
# q=311:
[25,96099],,
# q=313:
[22,97343],,,,
# q=317:
[24,99855],,,,,,,,,,,,,,
# q=331:
[25,108899],,,,,,
# q=337:
[30,112895],,,,,,
# q=343:
[18,116963],,,,
# q=347:
[28,119715],,
# q=349:
[24,121103],,,,
# q=353:
[35,123903],,,,,,
# q=359:
[29,128163],,
# q=361:
[41,129599],,,,,,
# q=367:
[28,133955],,,,,,
# q=373:
[26,138383],,,,,,
# q=379:
[23,142883],,,,
# q=383:
[29,145923],,,,,,
# q=389:
[32,150543],,,,,,,,
# q=397:
[30,156815],,,,
# q=401:
[30,159999],,,,,,,,
# q=409:
[34,166463],,,,,,,,,,
# q=419:
[34,174723],,
# q=421:
[22,176399],,,,,,,,,,
# q=431:
[35,184899],,
# q=433:
[36,186623],,,,,,
# q=439:
[36,191843],,,,
# q=443:
[34,195363],,,,,,
# q=449:
[37,200703],,,,,,,,
# q=457:
[38,207935],,,,
# q=461:
[35,211599],,
# q=463:
[42,213443],,,,
# q=467:
[38,217155],,,,,,,,,,,,
# q=479:
[36,228483],,,,,,,,
# q=487:
[37,236195],,,,
# q=491:
[37,240099],,,,,,,,
# q=499:
[38,248003],,,,
# q=503:
[38,252003],,,,,,
# q=509:
[39,258063],,,
# q=512:
[8,261120],,,,,,,,,
# q=521:
[40,270399],,
# q=523:
[37,272483],,,,,,
# q=529:
[36,278783],,,,,,,,,,,,
# q=541:
[38,291599],,,,,,
# q=547:
[39,298115],,,,,,,,,,
# q=557:
[42,309135],,,,,,
# q=563:
[37,315843],,,,,,
# q=569:
[40,322623],,
# q=571:
[40,324899],,,,,,
# q=577:
[41,331775],,,,,,,,,,
# q=587:
[41,343395],,,,,,
# q=593:
[39,350463],,,,,,
# q=599:
[39,357603],,
# q=601:
[42,359999],,,,,,
# q=607:
[43,367235],,,,,,
# q=613:
[47,374543],,,,
# q=617:
[36,379455],,
# q=619:
[41,381923],,,,,,
# q=625:
[28,389375],,,,,,
# q=631:
[45,396899],,,,,,,,,,
# q=641:
[45,409599],,
# q=643:
[42,412163],,,,
# q=647:
[46,417315],,,,,,
# q=653:
[46,425103],,,,,,
# q=659:
[43,432963],,
# q=661:
[44,435599],,,,,,,,,,,,
# q=673:
[48,451583],,,,
# q=677:
[52,456975],,,,,,
# q=683:
[48,465123],,,,,,,,
# q=691:
[53,476099],,,,,,,,,,
# q=701:
[46,489999],,,,,,,,
# q=709:
[54,501263],,,,,,,,,,
# q=719:
[51,515523],,,,,,,,
# q=727:
[51,527075],,
# q=729:
[23,529983],,,,
# q=733:
[52,535823],,,,,,
# q=739:
[52,544643],,,,
# q=743:
[53,550563],,,,,,,,
# q=751:
[50,562499],,,,,,
# q=757:
[44,571535],,,,
# q=761:
[54,577599],,,,,,,,
# q=769:
[51,589823],,,,
# q=773:
[59,595983],,,,,,,,,,,,,,
# q=787:
[56,617795],,,,,,,,,,
# q=797:
[56,633615],,,,,,,,,,,,
# q=809:
[57,652863],,
# q=811:
[57,656099],,,,,,,,,,
# q=821:
[54,672399],,
# q=823:
[54,675683],,,,
# q=827:
[59,682275],,
# q=829:
[59,685583],,,,,,,,,,
# q=839:
[59,702243],,
# q=841:
[53,705599],,,,,,,,,,,,
# q=853:
[65,725903],,,,
# q=857:
[61,732735],,
# q=859:
[57,736163],,,,
# q=863:
[57,743043],,,,,,,,,,,,,,
# q=877:
[62,767375],,,,
# q=881:
[67,774399],,
# q=883:
[58,777923],,,,
# q=887:
[63,784995],,,,,,,,,,,,,,,,,,,,
# q=907:
[69,820835],,,,
# q=911:
[65,828099],,,,,,,,
# q=919:
[65,842723],,,,,,,,,,
# q=929:
[66,861183],,,,,,,,
# q=937:
[62,876095],,,,
# q=941:
[67,883599],,,,,,
# q=947:
[67,894915],,,,,,
# q=953:
[68,906303],,,,,,,,
# q=961:
[65,921599],,,,,,
# q=967:
[64,933155],,,,
# q=971:
[69,940899],,,,,,
# q=977:
[69,952575],,,,,,
# q=983:
[70,964323],,,,,,,,
# q=991:
[70,980099],,,,,,
# q=997:
[66,992015],,,,,,,,,,,,
# q=1009:
[67],,,,
# q=1013:
[72],,,,,,
# q=1019:
[72],,
# q=1021:
[46],,,
# q=1024:
[18],];

CVEC_CalibrationTableNoCache := [,
# q=2:
[2,2,4,16,48,128,320,768],
# q=3:
[4,4,27,135,567,2187,8019,28431],
# q=4:
[1,8,80,512,2816,14336,69632,327680],
# q=5:
[2,15,175,1375,9375,59375,359375],,
# q=7:
[3,35,539,5831,55223,487403],
# q=8:
[1,48,832,10240,110592],
# q=9:
[3,63,1215,16767,203391],,
# q=11:
[3,99,2299,38599,570999],,
# q=13:
[4,143,3887,76895],,,
# q=16:
[2,224,7424,180224],
# q=17:
[3,255,8959,230911],,
# q=19:
[4,323,12635,363527],,,,
# q=23:
[5,483,22747,790855],,
# q=25:
[4,575,29375],,
# q=27:
[3,675,37179],,
# q=29:
[7,783,46255],,
# q=31:
[7,899,56699],
# q=32:
[3,960,62464],,,,,
# q=37:
[6,1295,97199],,,,
# q=41:
[8,1599,132799],,
# q=43:
[7,1763,153467],,,,
# q=47:
[9,2115,201019],,
# q=49:
[6,2303,228095],,,,
# q=53:
[8,2703,289327],,,,,,
# q=59:
[9,3363,400315],,
# q=61:
[12,3599,442799],,,
# q=64:
[3,3968,512000],,,
# q=67:
[9,4355,588059],,,,
# q=71:
[10,4899,700699],,
# q=73:
[10,5183,762047],,,,,,
# q=79:
[11,6083,967355],,
# q=81:
[6,6399],,
# q=83:
[11,6723],,,,,,
# q=89:
[14,7743],,,,,,,,
# q=97:
[16,9215],,,,
# q=101:
[16,9999],,
# q=103:
[14,10403],,,,
# q=107:
[17,11235],,
# q=109:
[15,11663],,,,
# q=113:
[16,12543],,,,,,,,
# q=121:
[11,14399],,,,
# q=125:
[10,15375],,
# q=127:
[18,15875],
# q=128:
[7,16128],,,
# q=131:
[18,16899],,,,,,
# q=137:
[17,18495],,
# q=139:
[15,19043],,,,,,,,,,
# q=149:
[16,21903],,
# q=151:
[15,22499],,,,,,
# q=157:
[19,24335],,,,,,
# q=163:
[20,26243],,,,
# q=167:
[20,27555],,
# q=169:
[20,28223],,,,
# q=173:
[21,29583],,,,,,
# q=179:
[22,31683],,
# q=181:
[20,32399],,,,,,,,,,
# q=191:
[23,36099],,
# q=193:
[24,36863],,,,
# q=197:
[24,38415],,
# q=199:
[19,39203],,,,,,,,,,,,
# q=211:
[23,44099],,,,,,,,,,,,
# q=223:
[24,49283],,,,
# q=227:
[28,51075],,
# q=229:
[28,51983],,,,
# q=233:
[29,53823],,,,,,
# q=239:
[26,56643],,
# q=241:
[30,57599],,
# q=243:
[22,58563],,,,,,,,
# q=251:
[31,62499],,,,,
# q=256:
[13,65024],
# q=257:
[28,65535],,,,,,
# q=263:
[29,68643],,,,,,
# q=269:
[29,71823],,
# q=271:
[30,72899],,,,,,
# q=277:
[30,76175],,,,
# q=281:
[31,78399],,
# q=283:
[31,79523],,,,,,
# q=289:
[29,82943],,,,
# q=293:
[29,85263],,,,,,,,,,,,,,
# q=307:
[30,93635],,,,
# q=311:
[34,96099],,
# q=313:
[34,97343],,,,
# q=317:
[35,99855],,,,,,,,,,,,,,
# q=331:
[30,108899],,,,,,
# q=337:
[37,112895],,,,,,
# q=343:
[27,116963],,,,
# q=347:
[34,119715],,
# q=349:
[38,121103],,,,
# q=353:
[35,123903],,,,,,
# q=359:
[39,128163],,
# q=361:
[62,129599],,,,,,
# q=367:
[36,133955],,,,,,
# q=373:
[41,138383],,,,,,
# q=379:
[54,142883],,,,
# q=383:
[42,145923],,,,,,
# q=389:
[43,150543],,,,,,,,
# q=397:
[44,156815],,,,
# q=401:
[44,159999],,,,,,,,
# q=409:
[45,166463],,,,,,,,,,
# q=419:
[46,174723],,
# q=421:
[60,176399],,,,,,,,,,
# q=431:
[47,184899],,
# q=433:
[43,186623],,,,,,
# q=439:
[48,191843],,,,
# q=443:
[49,195363],,,,,,
# q=449:
[49,200703],,,,,,,,
# q=457:
[50,207935],,,,
# q=461:
[51,211599],,
# q=463:
[51,213443],,,,
# q=467:
[51,217155],,,,,,,,,,,,
# q=479:
[53,228483],,,,,,,,
# q=487:
[54,236195],,,,
# q=491:
[54,240099],,,,,,,,
# q=499:
[55,248003],,,,
# q=503:
[55,252003],,,,,,
# q=509:
[50,258063],,,
# q=512:
[20,261120],,,,,,,,,
# q=521:
[52,270399],,
# q=523:
[52,272483],,,,,,
# q=529:
[49,278783],,,,,,,,,,,,
# q=541:
[54,291599],,,,,,
# q=547:
[54,298115],,,,,,,,,,
# q=557:
[55,309135],,,,,,
# q=563:
[56,315843],,,,,,
# q=569:
[56,322623],,
# q=571:
[57,324899],,,,,,
# q=577:
[57,331775],,,,,,,,,,
# q=587:
[58,343395],,,,,,
# q=593:
[59,350463],,,,,,
# q=599:
[59,357603],,
# q=601:
[60,359999],,,,,,
# q=607:
[60,367235],,,,,,
# q=613:
[61,374543],,,,
# q=617:
[61,379455],,
# q=619:
[61,381923],,,,,,
# q=625:
[37,389375],,,,,,
# q=631:
[63,396899],,,,,,,,,,
# q=641:
[64,409599],,
# q=643:
[64,412163],,,,
# q=647:
[64,417315],,,,,,
# q=653:
[65,425103],,,,,,
# q=659:
[65,432963],,
# q=661:
[66,435599],,,,,,,,,,,,
# q=673:
[67,451583],,,,
# q=677:
[67,456975],,,,,,
# q=683:
[68,465123],,,,,,,,
# q=691:
[69,476099],,,,,,,,,,
# q=701:
[70,489999],,,,,,,,
# q=709:
[70,501263],,,,,,,,,,
# q=719:
[71,515523],,,,,,,,
# q=727:
[72,527075],,
# q=729:
[34,529983],,,,
# q=733:
[73,535823],,,,,,
# q=739:
[73,544643],,,,
# q=743:
[74,550563],,,,,,,,
# q=751:
[75,562499],,,,,,
# q=757:
[75,571535],,,,
# q=761:
[76,577599],,,,,,,,
# q=769:
[76,589823],,,,
# q=773:
[77,595983],,,,,,,,,,,,,,
# q=787:
[78,617795],,,,,,,,,,
# q=797:
[79,633615],,,,,,,,,,,,
# q=809:
[80,652863],,
# q=811:
[81,656099],,,,,,,,,,
# q=821:
[82,672399],,
# q=823:
[82,675683],,,,
# q=827:
[82,682275],,
# q=829:
[82,685583],,,,,,,,,,
# q=839:
[83,702243],,
# q=841:
[77,705599],,,,,,,,,,,,
# q=853:
[85,725903],,,,
# q=857:
[85,732735],,
# q=859:
[85,736163],,,,
# q=863:
[86,743043],,,,,,,,,,,,,,
# q=877:
[87,767375],,,,
# q=881:
[88,774399],,
# q=883:
[88,777923],,,,
# q=887:
[88,784995],,,,,,,,,,,,,,,,,,,,
# q=907:
[90,820835],,,,
# q=911:
[91,828099],,,,,,,,
# q=919:
[91,842723],,,,,,,,,,
# q=929:
[92,861183],,,,,,,,
# q=937:
[93,876095],,,,
# q=941:
[94,883599],,,,,,
# q=947:
[94,894915],,,,,,
# q=953:
[95,906303],,,,,,,,
# q=961:
[97,921599],,,,,,
# q=967:
[96,933155],,,,
# q=971:
[97,940899],,,,,,
# q=977:
[97,952575],,,,,,
# q=983:
[109,964323],,,,,,,,
# q=991:
[99,980099],,,,,,
# q=997:
[99,992015],,,,,,,,,,,,
# q=1009:
[100],,,,
# q=1013:
[101],,,,,,
# q=1019:
[84],,
# q=1021:
[145],,,
# q=1024:
[40],];

CVEC_WinogradBounds :=
[ , 2560000, 2044900, 2256004, 1292769,, 2067844, 1406596, 1442401,, 1077444,
  , 1190281,,, 1324801, 10000000000,, 10000000000,,,, 10000000000,, 330625,, 
  455625,, 600625,, 619369, 859329,,,,, 561001,,,, 628849,, 620944,,,, 640000,
  , 611524,,,, 640000,,,,,, 640000,, 640000,,, 795664,,, 640000,,,, 640000,, 
  640000,,,,,, 640000,, 477481,, 876096,,,,,, 868624,,,,,,,, 870489,,,, 
  10000000000,, 876096,,,, 1071225,, 876096,,,, 10000000000,,,,,,,, 640000,,,
  , 640000,, 10000000000, 640000,,, 10000000000,,,,,, 10000000000,, 
  10000000000,,,,,,,,,, 10000000000,, 10000000000,,,,,, 10000000000,,,,,, 
  10000000000,,,, 10000000000,, 640000,,,, 10000000000,,,,,, 10000000000,, 
  10000000000,,,,,,,,,, 10000000000,, 10000000000,,,, 10000000000,, 
  10000000000,,,,,,,,,,,, 10000000000,,,,,,,,,,,, 10000000000,,,, 10000000000,
  , 10000000000,,,, 10000000000,,,,,, 10000000000,, 10000000000,, 10000000000,
  ,,,,,,, 10000000000,,,,, 660969, 10000000000,,,,,, 10000000000,,,,,, 
  10000000000,, 10000000000,,,,,, 10000000000,,,, 10000000000,, 10000000000,,,
  ,,, 10000000000,,,, 10000000000,,,,,,,,,,,,,, 10000000000,,,, 10000000000,, 
  10000000000,,,, 10000000000,,,,,,,,,,,,,, 10000000000,,,,,, 10000000000,,,,,
  , 10000000000,,,, 10000000000,, 10000000000,,,, 10000000000,,,,,, 
  10000000000,, 10000000000,,,,,, 10000000000,,,,,, 10000000000,,,,,, 
  10000000000,,,, 10000000000,,,,,, 10000000000,,,,,,,, 10000000000,,,, 
  10000000000,,,,,,,, 10000000000,,,,,,,,,, 10000000000,, 10000000000,,,,,,,,,
  , 10000000000,, 10000000000,,,,,, 10000000000,,,, 10000000000,,,,,, 
  10000000000,,,,,,,, 10000000000,,,, 10000000000,, 10000000000,,,, 
  10000000000,,,,,,,,,,,, 10000000000,,,,,,,, 10000000000,,,, 10000000000,,,,,
  ,,, 10000000000,,,, 10000000000,,,,,, 10000000000,,, 10000000000,,,,,,,,, 
  10000000000,, 10000000000,,,,,, 10000000000,,,,,,,,,,,, 10000000000,,,,,, 
  10000000000,,,,,,,,,, 10000000000,,,,,, 10000000000,,,,,, 10000000000,, 
  10000000000,,,,,, 10000000000,,,,,,,,,, 10000000000,,,,,, 10000000000,,,,,, 
  10000000000,, 10000000000,,,,,, 10000000000,,,,,, 10000000000,,,, 
  10000000000,, 10000000000,,,,,, 10000000000,,,,,, 10000000000,,,,,,,,,, 
  10000000000,, 10000000000,,,, 10000000000,,,,,, 10000000000,,,,,, 
  10000000000,, 10000000000,,,,,,,,,,,, 10000000000,,,, 10000000000,,,,,, 
  10000000000,,,,,,,, 10000000000,,,,,,,,,, 10000000000,,,,,,,, 10000000000,,,
  ,,,,,,, 10000000000,,,,,,,, 10000000000,, 10000000000,,,, 10000000000,,,,,, 
  10000000000,,,, 10000000000,,,,,,,, 10000000000,,,,,, 10000000000,,,, 
  10000000000,,,,,,,, 10000000000,,,, 10000000000,,,,,,,,,,,,,, 10000000000,,,
  ,,,,,,, 10000000000,,,,,,,,,,,, 10000000000,, 10000000000,,,,,,,,,, 
  10000000000,, 10000000000,,,, 10000000000,, 10000000000,,,,,,,,,, 
  10000000000,, 10000000000,,,,,,,,,,,, 10000000000,,,, 10000000000,, 
  10000000000,,,, 10000000000,,,,,,,,,,,,,, 10000000000,,,, 10000000000,, 
  10000000000,,,, 10000000000,,,,,,,,,,,,,,,,,,,, 10000000000,,,, 10000000000,
  ,,,,,,, 10000000000,,,,,,,,,, 10000000000,,,,,,,, 10000000000,,,, 
  10000000000,,,,,, 10000000000,,,,,, 10000000000,,,,,,,, 10000000000,,,,,, 
  10000000000,,,, 10000000000,,,,,, 10000000000,,,,,, 10000000000,,,,,,,, 
  10000000000,,,,,, 10000000000,,,,,,,,,,,, 10000000000,,,, 10000000000,,,,,, 
  10000000000,, 10000000000,,, 10000000000 ];


# Now read hostname-specific calibration data:
if IsBoundGlobal("IO_gethostname") then
    CVEC_hostname := IO_gethostname();
    CVEC_calibrationfile := Filename(
            DirectoriesPackageLibrary("cvec", "local"),
            Concatenation("calibration.", CVEC_hostname));
    if CVEC_hostname <> "" and CVEC_calibrationfile <> fail then
        Read(CVEC_calibrationfile);
        Info(InfoCVec,1,"Have read host-specific calibration file ",
                CVEC_calibrationfile);
    fi;
fi;

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
