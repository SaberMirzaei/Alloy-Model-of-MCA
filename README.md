PROJECT'S OVERVIEW
==================
This package presents a model for Consensus-based Auction (MCA) 
protocols Using Alloy language. MCA protocols
are an elegant approach to establish conflict-free distributed
allocations. In MCA-model module physical nodes (agents) have 
been modeled using Alloy signature pnode while virtual nodes 
have been modeled by vnodes. Each physical node has a set of 
capacitated connection with other physical nodes modeled using 
binary relation "pconnections" in the pnode signature. Module 
"utilityModule" can be used to add different policies. In the current 
model submodularity possibility of the utility fuction is modeled using 
two signatures "utility_submodular" and "utility_non_submodular".
Applying some slight changes in the model, new policies can be added
to the current model. Many existing Alloy "facts" regulate the behaviour of
the model such that the model present the correct behaviour of
distributed auction system. the state of an auction system is modeled
using "netState" signature which captures different properties of the system
such as the physical nodes' biding vectors, the number of floating messages
in the network and the time of the state. In order to test different
properties of the MCA protocols users can add any Alloy assertion in order
to check the corresponding properties. for instance the following assertion
is used the existance of the state that a distibuted auction system based 
on an MCA protocol reaches consensus (all the agents/physical nodes 
agree on the winners of the services/ virtual nodes):

  assert consensus{
	  1(#(netState) >= 10) implies (consensusPred[])
  }

This assertion is checked in the scope of four agents/physical nodes and
one service/virtual nodes using the following Alloy command:

  check consensus for 10 but exactly 4 pnode, exactly 1 vnode


RUNNING AND REQUIREMENTS
==================
In order to be able run this model, JRE and Alloy model checker are needed.

You can download Alloy model checker from:
http://alloy.mit.edu/alloy

running the model: 
	step1: Starting with executing the Alloy model checker and 
	openning The model's base module (namely MCA-model.als). Make sure to have
	all the required modules (releaseOutbidModule, utilityModule and valueModule) 
	in the same directory as the MCA-model.als file.
	
	step2: In order to check any specific assertion (such as predefine one concesus),
	from the "Execute" menue the corresponding assertion can be selected and checked.
	
	step3: If and assertion/model has some counter examples/instances, it can be
	depicted using the "Show" bottun. In case that the a counter example/instance does
	not exist the user will be notified that "No counter example exists" on the message
	panel on the right.

PEOPLE
==================
Saber Mirzaei and
Flavio Esposito
