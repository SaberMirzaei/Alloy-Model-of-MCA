sig value{succ: set value, pre: set value}
one sig zero extends value{}{no pre}
one sig max extends value{} {no succ}
one sig valOne  extends value{}{pre = zero}
one sig valTwo  extends value{}{pre = (zero+valOne)}
one sig valThree  extends value{}{pre = (zero+valOne+valTwo)}
one sig valFour  extends value{}{pre = (zero+valOne+valTwo+valThree)}
one sig valFive  extends value{}{pre = (zero+valOne+valTwo+valThree+valFour)}
one sig valSix  extends value{}{pre = (zero+valOne+valTwo+valThree+valFour+valFive)}
/*one sig valSeven  extends value{}{pre = (zero+valOne+valTwo+valThree+valFour+valFive+valSix)}
one sig valEight  extends value{}{pre = (zero+valOne+valTwo+valThree+valFour+valFive+valSix+valSeven)}
one sig valNine  extends value{}{pre = (zero+valOne+valTwo+valThree+valFour+valFive+valSix+valSeven+valEight)}
one sig valTen  extends value{}{pre = (zero+valOne+valTwo+valThree+valFour+valFive+valSix+valSeven+valEight+valNine)}
one sig valEleven  extends value{}{pre = (zero+valOne+valTwo+valThree+valFour+valFive+valSix+valSeven+valEight+valNine+valTen)}
one sig valTwelve  extends value{}{pre = (zero+valOne+valTwo+valThree+valFour+valFive+valSix+valSeven+valEight+valNine+valTen+valEleven)}
one sig valThirteen  extends value{}{pre = (zero+valOne+valTwo+valThree+valFour+valFive+valSix+valSeven+valEight+valNine+valTen+valEleven+valTwelve)}
one sig valFourteen  extends value{}{pre = (zero+valOne+valTwo+valThree+valFour+valFive+valSix+valSeven+valEight+valNine+valTen+valEleven+valTwelve+valThirteen)}
one sig valFifteen  extends value{}{pre = (zero+valOne+valTwo+valThree+valFour+valFive+valSix+valSeven+valEight+valNine+valTen+valEleven+valTwelve+valThirteen+valFourteen)}*/

fact {one v:value | no v.succ}
fact {one v:value | no v.pre}
fact {all v:value |  !(v in v.pre) and !(v in v.succ) and no(v.succ & v.pre)}
fact {all disj v1,v2,v3: value | 
		((v1 in v2.pre and v2 in v3.pre) implies (v1 in v3.pre)) and
		((v1 in v2.succ and v2 in v3.succ) implies (v1 in v3.succ))
}
fact {all disj v1,v2: value | (v1 in v2.pre) or (v1 in v2.succ)}
fact {all disj v1,v2: value | (v1 in v2.pre) implies ( (v2 in v1.succ) and !(v1 in v2.succ) )}
fact {all disj v1,v2: value | (v2 in v1.succ) implies ( (v1 in v2.pre) and !(v2 in v1.pre) )}

pred valL(v1,v2: value){
	v1 in v2.pre
}

pred valG(v1,v2: value){
	v1 in v2.succ
}

pred valLE(v1,v2: value){
	(v1 = v2) or (v1 in v2.pre) 
}

pred valGE(v1,v2: value){
	(v1 = v2) or (v1 in v2.succ)
}
assert test{one v:value| #v.pre = 10}
//check test for exactly 15 value
run{} for exactly 8 value
