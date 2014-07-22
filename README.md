OVERVIEW
==================
This package presents a model for Consensus-based Auction (MCA) protocols Using Alloy language. 

MCA protocols are an elegant approach to establish conflict-free distributed allocations for a wide range of distributed system applications. As a case study, we use a virtual network embedding application  


In our MCA-model module, physical nodes (agents) have been modeled using the Alloy signature "pnode" and virtual nodes have been modeled by the "vnodes" signature. Each physical node has a set of capacitated connection with other physical nodes modeled using binary relation "pconnections" in the "pnode" signature. 


The Module "utilityModule" can be used to add different MCA policies. In our  model we assume the utility function that agents (physical node) use to bid on items (virtual nodes) to be submodularity, and we use model it using two signatures "utility_submodular" and "utility_non_submodular". 

With minor changes, new policies can be added to the current model. The existing Alloy "facts" that we provide as examples model the correct behaviour of a distributed auction system in the MCA protocol. 


The state of the auction system is modelled using the "netState" signature, which captures different properties of the system such as the physical nodes' bidding vectors, the number of floating messages in the physical network of agents, and the generation time of the state. In order to test different properties of the MCA protocols, users can add additional Alloy assertions in order to check the corresponding properties. For instance, the following assertion is used to check the existence of a consensus state for the distributed auction, i.e., all the agents (physical nodes) agree on the winners of the items (virtual nodes):

	assert consensus{
		1(#(netState) >= 10) implies (consensusPred[])
	}

This assertion is checked in the scope of four agents/physical nodes and
one service/virtual nodes using the following Alloy command:

	check consensus for 10 but exactly 4 pnode, exactly 1 vnode


INSTALLATION AND RUNNING INSTRUCTIONS
==================

To run any Alloy model, JRE and the Alloy model checker need to be installed.

The Alloy model checker can be downloaded from: http://alloy.mit.edu/alloy

Running 

	Step1: Start with executing the Alloy model checker and 
	open the model's base module MCA-model.als. Make sure that
	all the required modules (releaseOutbidModule, utilityModule and valueModule) 
	are in the same directory as the MCA-model.als file.

	Step2: In order to check a specific assertion select
	from the "Execute" menu, the corresponding assertion name (e.g., "consensus").

	Step3: If an assertion finds a counter example, this can be
	seen using the "Show" button. In case that such counter example does
	not exist the user will be notified that "No counter example exists" on the message
	panel on the right.


PUBLICATIONS
==================
Mirzaei, Saber; Esposito, Flavio.
An Alloy Verification Model for Consensus-Based Auction Protocols,
July 15, 2014. Tecnical Report BU-CS-TR-2014-004 (under submission)
link:URL_to_wiki[Link Text]
[PDF][PS][Abstract]

[References]
Boston University Alloy Project. http://csr.bu.edu/alloy
MIT Alloy Project. http://alloy.mit.edu/alloy/
