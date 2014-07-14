ABSTRACT
==================
Max Consensus-based Auction (MCA) protocols
are an elegant approach to establish conflict-free distributed
allocations in a wide range of network utility maximization
problems, as they provide bounds on the time to solution,
and on the performance with respect to the optimal network
utility. Agents independently bid on a set of items, and exchange
their bids with their first hop-neighbors for a distributed (maxconsensus)
winner determination. The use of MCA protocols
was proposed, e:g:, to solve the task allocation problem for
a fleet of unmanned aerial vehicles, or in distributed virtual
network management applications. Misconfigured or malicious
agents participating in a MCA, or an incorrect instantiation of
policies can lead to oscillations of the protocol, causing, e:g:,
Service Level Agreement (SLA) violations.
In this work, we propose a formal, machine-readable, Max-
Consensus Auction model, encoded in the Alloy lightweight
modeling language. The model consists of a network of agents
applying the MCA mechanisms, instantiated with potentially
different policies, and a set of predicates to analyze its convergence
properties. We were able to verify that MCA is
not resilient against rebidding attacks, and that the protocol
fails (to achieve a conflict-free resource allocation) for given
combination of policies. Our model can be used to verify,
with a "push-button" analysis, the convergence of the MCA
mechanism to a conflict-free allocation of for a wide range of
policy instantiations.



RUNNING AND REQUIREMENTS
==================
In order to be able run this model, JRE and Alloy model checker are needed.
You can download Alloy model checker from:
http://alloy.mit.edu/alloy


PEOPLE
==================
Saber Mirzaei and
Flavio Esposito
