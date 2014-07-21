PROJECT'S OVERVIEW
==================
This package presents a model for Consensus-based Auction (MCA) protocols Using Alloy language. 

[ SPACE ]

MCA protocols are an elegant approach to establish conflict-free distributed allocations for a wide range of distributed system applications. As a case study, we use a virtual network embedding application  

[ SPACE ]

In our MCA-model module, physical nodes (agents) have been modeled using the Alloy signature "pnode" and virtual nodes have been modeled by the "vnodes" signature. Each physical node has a set of capacitated connection with other physical nodes modeled using binary relation "pconnections" in the "pnode" signature. 

[ SPACE ]

The Module "utilityModule" can be used to add different MCA policies. In our  model we assume the utility function that agents (physical node) use to bid on items (virtual nodes) to be submodularity, and we use model it using two signatures "utility_submodular" and "utility_non_submodular". 

[ SPACE ]

With minor changes, new policies can be added to the current model. The existing Alloy "facts" that we provide as examples model the correct behaviour of a distributed auction system in the MCA protocol. 

[ SPACE ]


The state of the auction system is modelled using the "netState" signature, which captures different properties of the system such as the physical nodes' bidding vectors, the number of floating messages in the physical network of agents, and the generation time of the state. In order to test different properties of the MCA protocols, users can add additional Alloy assertions in order to check the corresponding properties. For instance, the following assertion is used to check the existence of a consensus state for the distributed auction, i.e., all the agents (physical nodes) agree on the winners of the items (virtual nodes):

	assert consensus{
		1(#(netState) >= 10) implies (consensusPred[])
	}

This assertion is checked in the scope of four agents/physical nodes and
one service/virtual nodes using the following Alloy command:

	check consensus for 10 but exactly 4 pnode, exactly 1 vnode


RUNNING AND REQUIREMENTS
==================
In order to be to able run this model, JRE and Alloy model checker are needed.

You can download Alloy model checker from:
http://alloy.mit.edu/alloy

running the model: 

	step1: Starting with executing the Alloy model checker and 
	openning The model's base module (namely MCA-model.als). Make sure to have
	all the required modules (releaseOutbidModule, utilityModule and valueModule) 
	in the same directory as the MCA-model.als file.
	
	step2: In order to check any specific assertion (such as predefine one "consensus"),
	from the "Execute" menu, the corresponding assertion can be selected and checked.
	
	step3: If and assertion/model has any counter example/instance, it can be
	depicted using the "Show" button. In case that the a counter example/instance does
	not exist the user will be notified that "No counter example exists" on the message
	panel on the right.

PEOPLE
==================
Saber Mirzaei and
Flavio Esposito
