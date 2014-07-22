open valueModule
open utilityModule
open releaseOutbidModule
open util/ordering[netState]

one sig NULL{}
//Physical Node
sig pnode{
	pcp: one value, // cpacity of a physical node
	pid: one value, 
	initBidTriples:set bidTriple,
	pconnections: some pnode,
	p_T: one Int,
	P_U: one utility,
	P_RO: one release_outbid
}

//VIRTUAL Node
sig vnode{vid: one value}


//Requested Slice is model
one sig slice{vns: set vnode, sInitiator: one pnode}


// A message from a pnode to another about it's view
sig message{
	mSender: one pnode,
	mReceiver: one pnode,
	mBidTriples: set bidTriple
}

// bidVector is the image of pnode bvPn winners represents the pnode that is the assumed winner, 
// winnerBids is the bid value of the winner pnode equivalent to b vector, initBidsOn is the bid 
// that the each pnode has made
sig bidVector{
	bvPn:one pnode,
	bvBidTriples: set bidTriple,
	excludedVN: set vnode /// it models the set of vnodes that bvPn has been outbid on
}

sig netState {bidVectors: some bidVector, time: one value,buffMsgs: set message}

sig bidTriple{
	bidTriple_v: one vnode,
	bidTriple_b: one value, // models the value of the bid
	bidTriple_t: one value,// models the time of the bid
	bidTriple_w: one (pnode + NULL) // models the winner of the bid
}

fun findBidVecByPn(bvs: set bidVector, p:one pnode): one bidVector {bvPn.p & bvs}

// returns all the vnode that the owner of a bidvector is winning
fun  vnodesWonBy(bv: bidVector): set vnode {(bidTriple_w.(bv.bvPn) & bv.bvBidTriples).bidTriple_v}

fun findBidTriple(bts: set bidTriple, v: vnode): one bidTriple {bidTriple_v.v & bts}


/////////////////// facts on pnode /////////////////////// begin /////////////////
// atleast some pnodes make some bids
fact{!(pnode.initBidTriples.bidTriple_b = zero)}

// If the bid is zero then the winner must be NULL and vise versa
fact{all bt: bidTriple |
	(bt.bidTriple_b = zero implies (bt.bidTriple_t = zero and bt.bidTriple_w = NULL)) and 
	(bt.bidTriple_w = NULL implies (bt.bidTriple_t = zero and bt.bidTriple_b = zero)) 
}

//submodularity  initially and in each bidvector
fact {
	all bv:bidVector | 
	(
		(bv.bvPn.P_U = utility_submodular) implies
			all disj v1, v2: vnodesWonBy[bv] | 
				valL[v1.vid, v2.vid] implies
				(
				(valL[findBidTriple[bv.bvBidTriples, v1].bidTriple_t, findBidTriple[bv.bvBidTriples, v2].bidTriple_t]) and 
				(valGE[findBidTriple[bv.bvBidTriples, v1].bidTriple_b, findBidTriple[bv.bvBidTriples, v2].bidTriple_b])
				)
			)
	)
}


//no double edges or more and bidirected connections and upload = download capacity and pid must be unique
fact{all disj pn1,pn2:pnode |( pn1.pid != pn2.pid) and (pn1 in pn2.pconnections <=> pn2 in pn1.pconnections)}

//graph is connected physical node capacity and pID must be non negative and no self loop 
fact{all pn:pnode | (pn in (slice.sInitiator). *pconnections) and no (pn & pn.pconnections) and (pn.p_T <= #(vnode))}

// pnodes are the winner for those vnodes that they make positive bid
fact{all pn: pnode| all bt: pn.initBidTriples |
				!(bt.bidTriple_b = zero) implies (bt.bidTriple_w = pn)
										  else (bt.bidTriple_w = NULL)
}

//each node initially must make #(vnode) bids which can be NULL
fact {all pn: pnode |	
	#(pn.initBidTriples) = #(vnode) and 
	pn.initBidTriples.bidTriple_v = vnode
} 

//bid values and bid times must be possitive
//fact {all bt: bidTriple| bt.bidTriple_b >= 0 and bt.bidTriple_t  >= 0}

// initial bid times must be smaller that the time of the first state
fact {all initB : pnode.initBidTriples| valL[initB.bidTriple_t, first.time]}


// vid must be unique
fact{all disj vn1,  vn2: vnode | /*vn1.vid > 0 and */vn1.vid != vn2.vid   }



// message m, should containd the view m.mSender for all the vnodes
fact{all m:message |
	#(m.mBidTriples) = #(vnode) and
	m.mBidTriples.bidTriple_v = vnode and 
	m.mSender != m.mReceiver
}

//don't have dangling messages
fact {all m:message | some s:netState | m in s.buffMsgs}


fact {all s: netState, s': s.next | one m:message | messaging[s, s', m]}


fact {all s: netState |
	#(s.bidVectors) = #(pnode) and 
	(s.bidVectors.bvPn = pnode) /*and 
	s.time > 0*/
}


//the bid vector of the first state should contain the initial view of the all pnodes
fact {all b: first.bidVectors |
	b.bvBidTriples = b.bvPn.initBidTriples and
	no b.excludedVN
}

// If a Pnode is the slice initiator then there should be some buffered messages for each one
// of the connections orifinating from that pnode
fact { all p:pnode | 
		p in slice.sInitiator.pconnections 
			implies (one m:first.buffMsgs | 
							m.mReceiver = p and 
							m.mSender = slice.sInitiator and 
							m.mBidTriples = slice.sInitiator.initBidTriples
					)
}

//and there should not be other msgs (ref. previous fact)
fact{#(first.buffMsgs) = #(slice.sInitiator.pconnections)}

/////////////////// facts on first state /////////////////////// end /////////////////

// we don't have empty slices
fact {slice.vns = vnode}

/////////////////// facts on bidVector /////////////////////// begin /////////////////
// If a vnode is added to the exclude list then there should not be a bid value or time 
// for it assigned to the pnode of the bidvector
fact{all b:bidVector | all xv: b.excludedVN | !( findBidTriple[b.bvBidTriples, xv].bidTriple_w in (NULL+b.bvPn))}


//every state keeps track of all vnodes
fact {all b:bidVector | 
			#(b.bvBidTriples) = #(vnode) and
			b.bvBidTriples.bidTriple_v = vnode 
}

//bidVectors are used by some netStates//can be removed
fact{all b:bidVector | some s: netState | b in s.bidVectors }


/////////////////// facts on bidVector /////////////////////// end /////////////////


pred messaging(s, s': netState, m:message){
	bidVectorsConsistency[s, s', m] and
	valG[s'.time, s.time] and
	(s.buffMsgs - s'.buffMsgs) = m and
	(s.bidVectors.excludedVN in s'.bidVectors.excludedVN) and
//	buffMsgConsitency[s, s', m.mReceiver, m] and
	(
	allVnodesDoNothing[s,m]  
			implies  
					(
						#(s'.buffMsgs - s.buffMsgs) = 0 and
						s'.bidVectors = s.bidVectors
					)
			else (m.mReceiver.P_RO = release_outbid_yes) implies
					(
						 checkAllOfVnodes[s, s', m] and
						 broadCastToAll[s',m]
					)
			else (
				#(s'.buffMsgs - s.buffMsgs) = #( m.mReceiver.pconnections) and 
				( 
	 				(one v:vnode | (outBid[s, v, m] and updateAndRebid[s, s', v, m]))
						or
					((no v:vnode | outBid[s, v, m]) and  checkAllOfVnodes[s, s', m]) 
				) and
				broadCastToAll[s',m]
				)
	)
}

//update the bidvector for outbid vnode v and release the others
pred updateAndRebid(s,s':netState, v: vnode, m:message){
	((findBidVecByPn[s'.bidVectors, m.mReceiver].excludedVN - findBidVecByPn[s.bidVectors, m.mReceiver].excludedVN) = v) 
	and
	(all v':  (vnodesWonBy[findBidVecByPn[s.bidVectors, m.mReceiver]] - v) 
		| valG[v'.vid, v.vid] implies (releaseOrRebid[s, s',v',m.mReceiver])
	else (checkBidAndTime[s, s', v', m]) )
	and
	(all v': (vnode - vnodesWonBy[findBidVecByPn[s.bidVectors, m.mReceiver]]) | checkRestOfVnodes[s,s',v',m] )
	and
	outBidUpdateAndRebroadcast[s,s',v,m]
}

//check the updates for the vnodes that other pnodes are winning
pred checkRestOfVnodes(s,s':netState, v: vnode, m:message){
	(	findBidTriple[m.mBidTriples, v].bidTriple_w  = findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w   
		and ( findBidTriple[m.mBidTriples, v].bidTriple_b  = findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_b ) 
		and ( valLE[findBidTriple[m.mBidTriples, v].bidTriple_t , findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_t] )) 
	implies (doNothing[s, s', v, m])
			
	//this rule covers all the tie breaking situations -> R!=S and R!={Null+s} and S!={Null+r}
	else 			( !( findBidTriple[m.mBidTriples, v].bidTriple_w  = findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w ) 
		and !( findBidTriple[m.mBidTriples, v].bidTriple_w  in (m.mReceiver + NULL)) 
		and !( findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w  in (m.mSender + NULL)) 
		and ( findBidTriple[m.mBidTriples, v].bidTriple_b  = findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_b )  
		and ( valL[findBidTriple[m.mBidTriples, v].bidTriple_w .pid, findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w .pid])  ) 
	implies (updateAndRebroadcast[s, s', v, m])
			
	else			( !( findBidTriple[m.mBidTriples, v].bidTriple_w  in (m.mReceiver+m.mSender+NULL)) 
		and ( findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w  in (m.mSender + NULL) )  ) 
	implies (updateAndRebroadcast[s, s', v, m])
			
	else 			( !( findBidTriple[m.mBidTriples, v].bidTriple_w  in (m.mReceiver+m.mSender+NULL)) 
		and !( findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w  in (m.mReceiver +m.mSender + findBidTriple[m.mBidTriples, v].bidTriple_w  + NULL) )  
		and  !( findBidTriple[m.mBidTriples, v].bidTriple_b  = findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_b ) 
		and ( valGE[findBidTriple[m.mBidTriples, v].bidTriple_t , findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_t] )  ) 
	implies (updateAndRebroadcast[s, s', v, m])

	else 			( ( (findBidTriple[m.mBidTriples, v].bidTriple_w + findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w)  in (NULL+m.mSender) ) 
		and (findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w != findBidTriple[m.mBidTriples, v].bidTriple_w )  ) 
	implies (updateAndRebroadcast[s, s', v, m])

	
	else 			( ( findBidTriple[m.mBidTriples, v].bidTriple_w  = NULL ) 
		and !( findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w  in (m.mReceiver +m.mSender + NULL) )  
		and ( valG[findBidTriple[m.mBidTriples, v].bidTriple_t , findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_t] ) ) 
		implies (updateAndRebroadcast[s, s', v, m])

	else 			( ( findBidTriple[m.mBidTriples, v].bidTriple_w  = m.mSender) 
		and ( findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w  = m.mSender)  
		and ( valG[findBidTriple[m.mBidTriples, v].bidTriple_t , findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_t] )  ) 
	implies (updateAndRebroadcast[s, s', v, m])

	else 			(  ( findBidTriple[m.mBidTriples, v].bidTriple_w  = m.mSender) 
		and !( findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w  in (m.mReceiver +m.mSender + NULL) )  
		and  ( valG[findBidTriple[m.mBidTriples, v].bidTriple_b , findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_b] 
				or 
			valG[findBidTriple[m.mBidTriples, v].bidTriple_t , findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_t] )  ) 
	implies (updateAndRebroadcast[s, s', v, m])

	else 			( ( findBidTriple[m.mBidTriples, v].bidTriple_w  = m.mReceiver) 
		and ( findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w  = m.mSender)) 
	implies (resetAndRebroadcastStar[s, s', v, m])

	else 			( ( findBidTriple[m.mBidTriples, v].bidTriple_w  = m.mReceiver) 
		and ( findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w  = NULL)) 
	implies (rebroadcastStar[s, s', v, m]) 
	
	else			rebroadcast[s, s', v, m]
}

// release or rebid
pred releaseOrRebid(s, s':netState, v:vnode, p:pnode){
	one bv: s'.bidVectors | (bv.bvPn = p) and 
			( (findBidTriple[bv.bvBidTriples, v].bidTriple_w =  p 
				and valG[findBidTriple[bv.bvBidTriples, v].bidTriple_b, zero] 
				and valL[findBidTriple[bv.bvBidTriples, v].bidTriple_t, s'.time] 
				and valG[findBidTriple[bv.bvBidTriples, v].bidTriple_t , s.time]) 
			or 
			(findBidTriple[bv.bvBidTriples, v].bidTriple_w =  NULL 
				and findBidTriple[bv.bvBidTriples, v].bidTriple_b = zero 
				and findBidTriple[bv.bvBidTriples, v].bidTriple_t = zero)
			)
}

//check if vnode v if has the smallest id and is being outbid
pred outBid(s: netState, v: vnode, m: message){
	(
		!( findBidTriple[m.mBidTriples, v].bidTriple_w in (m.mReceiver+NULL)) and 
		( findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w  = m.mReceiver)  and 
		( 
			valG[findBidTriple[m.mBidTriples, v].bidTriple_b , findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_b]  or 
			(
				( findBidTriple[m.mBidTriples, v].bidTriple_b  = findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_b )  and 
				( valL[findBidTriple[m.mBidTriples, v].bidTriple_w.pid, findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w .pid])  
			)
		)
	) and
	(all v': (vnode - v)|
		( !( findBidTriple[m.mBidTriples, v'].bidTriple_w in (m.mReceiver+NULL)) 
				and ( findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v'].bidTriple_w = m.mReceiver)  
				and ( valG[findBidTriple[m.mBidTriples, v'].bidTriple_b, findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v'].bidTriple_b] 
					or (( findBidTriple[m.mBidTriples, v'].bidTriple_b = findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v'].bidTriple_b)  
				and ( valL[findBidTriple[m.mBidTriples, v'].bidTriple_w.pid, findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v'].bidTriple_w.pid])  )))  
	implies (valG[v'.vid, v.vid])  )
}



//this pred checks all the situations including those that receiver think is the winner which are not covered by checkRestOfVnodes()
pred checkAllOfVnodes(s, s': netState, m: message){
	all v: vnode |(
			( !( findBidTriple[m.mBidTriples, v].bidTriple_w  in (m.mReceiver + NULL)) 
				and ( findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w  = m.mReceiver)  
				and ( valG[findBidTriple[m.mBidTriples, v].bidTriple_b, findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_b] )  ) 
	implies (updateAndRebroadcast[s, s', v, m])

			else			( !( findBidTriple[m.mBidTriples, v].bidTriple_w  in (m.mReceiver+NULL)) 
				and ( findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w  = m.mReceiver)  
				and ( valL[findBidTriple[m.mBidTriples, v].bidTriple_b, findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_b] )  ) 
			implies (updateTimeAndRebroadcast[s, s', v, m])

			else  		checkRestOfVnodes[s, s', v, m]
	)
}
/////////////////////////////////////pred on messaging /////////////////////////begin//////////////////////

//only the bidvector of the receiver may change
pred bidVectorsConsistency(s, s': netState, m: message){
	all pn: (pnode - m.mReceiver) | findBidVecByPn[s'.bidVectors, pn] = findBidVecByPn[s.bidVectors, pn]
}

//All the msgs that are in s' and not in s, their sender can be only r
pred buffMsgConsitency (s,s': netState, r: pnode, m: message){
	( allVnodesDoNothing[s,m] implies  (#(s'.buffMsgs - s.buffMsgs) = 0)
		else (#(s'.buffMsgs - s.buffMsgs) = #(r.pconnections)) 
	)
}


pred allVnodesDoNothing( s: netState, m: message){
all v: vnode |	
	(findBidTriple[m.mBidTriples, v].bidTriple_w  = findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w)   and 
	( findBidTriple[m.mBidTriples, v].bidTriple_b  = findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_b ) and 
	( valLE[findBidTriple[m.mBidTriples, v].bidTriple_t , findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_t] )
}


pred outBidUpdateAndRebroadcast(s, s': netState, v: vnode, m: message){
//	(cheat[s,s',v,m] and !fairPlay[s,s',v,m] )
//or 
	(fairPlay[s,s',v,m] )//and !cheat[s,s',v,m] )
}


pred fairPlay(s, s': netState, v: vnode, m: message){
	(one bv: s'.bidVectors | 
		(bv.bvPn = m.mReceiver) and 
		(findBidTriple[bv.bvBidTriples, v]  =  findBidTriple[m.mBidTriples, v] )
	)
}



pred updateAndRebroadcast(s, s': netState, v: vnode, m: message){
	(one bv: s'.bidVectors | 
		(bv.bvPn = m.mReceiver) and 
		(findBidTriple[bv.bvBidTriples, v] =  findBidTriple[m.mBidTriples, v]) 
	)
}


/*pred cheat(s, s': netState, v: vnode, m: message){
(one bv: s'.bidVectors | (bv.bvPn = m.mReceiver) and (v.(bv.winners) =  m.mReceiver) and (v.(bv.winnerBids) =  add[v.(m.msgWinnerBids),1] ) and (v.(bv.bidTimes) =  add[v.(m.msgBidTimes),1])) /// make sure about the time
	and
 (all c:  m.mReceiver.pconnections   | 
	one m': message | 
		(m'.mSender = m.mReceiver) 
		and (m'.mReceiver = c ) 
		and (m'.mWinners = findBidVecByPn[s'.bidVectors, m.mReceiver].winners) 
		and (m'.msgWinnerBids = findBidVecByPn[s'.bidVectors, m.mReceiver].winnerBids) 
		and (m'.msgBidTimes = findBidVecByPn[s'.bidVectors, m.mReceiver].bidTimes) and (m' in s'.buffMsgs))
}*/


pred updateTimeAndRebroadcast(s, s': netState, v: vnode, m: message){///////make sure about the povalue that time must be updated to
	(one bv: s'.bidVectors | 
		(bv.bvPn = m.mReceiver) and 
		(findBidTriple[bv.bvBidTriples, v].bidTriple_w =  findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w) and 
		(findBidTriple[bv.bvBidTriples, v].bidTriple_b =  findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_b ) and 
		(
			(valGE[findBidTriple[m.mBidTriples, v].bidTriple_t, findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_t]) 
				implies (findBidTriple[bv.bvBidTriples, v].bidTriple_t = findBidTriple[m.mBidTriples, v].bidTriple_t)
				else (findBidTriple[bv.bvBidTriples, v].bidTriple_t = findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_t )
		)
	)
}


pred doNothing(s, s': netState, v: vnode, m: message){
    (one bv: s'.bidVectors | 
		(bv.bvPn = m.mReceiver) and 
		(findBidTriple[bv.bvBidTriples, v] =  findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v])
	)
}



pred rebroadcast(s, s': netState, v: vnode, m: message){
	doNothing[s,s',v,m]
}


pred resetAndRebroadcastStar(s, s': netState, v: vnode, m: message){
	(one bv: s'.bidVectors | 
		(bv.bvPn = m.mReceiver) and 
		(findBidTriple[bv.bvBidTriples, v].bidTriple_w =  NULL) and 
		(findBidTriple[bv.bvBidTriples, v].bidTriple_b = zero) and 
		(findBidTriple[bv.bvBidTriples, v].bidTriple_t =  s'.time) 
	)
}


pred rebroadcastStar(s, s': netState, v: vnode, m: message){
	 (one bv: s'.bidVectors | 
		(bv.bvPn = m.mReceiver) and 
		(findBidTriple[bv.bvBidTriples, v].bidTriple_w =  findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_w) and 
		(findBidTriple[bv.bvBidTriples, v].bidTriple_b =  findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_b ) and 
		(findBidTriple[bv.bvBidTriples, v].bidTriple_t =  s'.time) 
	)

}


pred broadCastToAll(s': netState, m: message){
	all c: m.mReceiver.pconnections  | one m': message | 
		(m'.mSender = m.mReceiver) and (m'.mReceiver = c ) and 
		(m'.mBidTriples = findBidVecByPn[s'.bidVectors, m.mReceiver].bvBidTriples) and
		(m' in s'.buffMsgs)
}


pred checkBidAndTime(s, s': netState, v: vnode, m: message){
	(
		!(findBidTriple[m.mBidTriples, v].bidTriple_w in (m.mReceiver + NULL)) and 
		( valL[findBidTriple[m.mBidTriples, v].bidTriple_b, findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_b]) 
	) implies (updateTimeAndRebroadcast[s, s', v, m])
	else (
		(findBidTriple[m.mBidTriples, v].bidTriple_w = m.mReceiver) and 
		(findBidTriple[m.mBidTriples, v].bidTriple_t = findBidTriple[findBidVecByPn[s.bidVectors, m.mReceiver].bvBidTriples, v].bidTriple_t) 
	) implies (doNothing[s, s', v, m])
	else 
		rebroadcast[s, s', v, m]
}
/////////////////////////////////////pred on messaging /////////////////////////begin//////////////////////

pred consensusPred{
	some s: (netState - first) | all disj bv1,bv2: s.bidVectors | all v: vnode |
		(
			(findBidTriple[bv1.bvBidTriples, v].bidTriple_w = findBidTriple[bv2.bvBidTriples, v].bidTriple_w) and
			(findBidTriple[bv1.bvBidTriples, v].bidTriple_b = findBidTriple[bv2.bvBidTriples, v].bidTriple_b) and
			(findBidTriple[bv1.bvBidTriples, v].bidTriple_t = findBidTriple[bv2.bvBidTriples, v].bidTriple_t)
		)
}




assert consensus{
	(#(netState) >= 10) implies (consensusPred[])
}
check consensus for 10 but exactly 16 value, exactly 2 pnode, exactly 2 vnode

assert numOfStates{
	!(#(netState) >= 10)
}
check numOfStates for 10 but exactly 16 value, exactly 2 pnode, exactly 2 vnode
