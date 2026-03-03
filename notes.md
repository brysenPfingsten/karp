# <2026-02-05 Tue>

# Something to describe the entities in the reductions
# Gadgets, clauses

Maybe you say in the problem description the semantic entities that your
description imposes on the raw graph structure, and you have to do ...
something ... to label that. For graphs you get lucky because there are
only nodes and edges, and the nodes are sufficient to determine the entities?
But maybe that it works for graphs is sufficient?

** TODO -- find other weird zany kinds of reductions across wild
classes of problem, something where it's fundamentally different from
clause, graph, mapping, and not reduced into them, and see about that.

So somehow the *structure* of the semantic entities in teh problme is imposed by the
problem description, but the order that those things are created is imposed by the
forward instance thing.

** We could, but don't need to right now, go pretty up the surface syntax to make our
graphing work with all of the other syntax sugar in the karp reduction language rn.

** TODO: can you actually union directed edges and undirected edges?
** TODO: can you actually create a graph with a combination of directed and undirected edges? -- either a directed or undirected graph

## Next

We are going to work on I think either subset-sum, or something else where you have a mapping based
description

### Another idea, would be to turn 3cnf into a mapping, which should be trivial

### Ever worthwhile to go back and see if we can improve the hamiltonian?
We tried to eliminate 2 nodes on the left and one on the right in our would-be reduction fix-up
But, that broke. It might be though that we can still remove one of the two on the left, and *that* would still work.

### We should add notes about what works and what doesn't, and consider if the next step wants to be a
separate fork or continue from this one?

Is this just a spike or what?




# Highlight new things added to viz
We're not eating clauses. Highlight the clause as the clique is being formed then grey it out once it is done.

# Make nodes and edges not bounce around after stepping
2 Choices
1. Draw whole graph white then make them black as they appear
2. Draw whole graph, remember coordinates, use those coordinates when they appear
New Idea
- Have the user declare more information about the data structure in the problem definition
  - E.g., define the gadgets in the problem definition and annotate them as being added in the reduction

# Draw two-way directed edges as two lines
Graphviz issue
1. Hack the graphviz function with differing attributes
2. Roll our own graph -> dot function

# Time to start working on different types of problems
- Mappings
  - Subset sum
  - Strategic Advertising

# Start thinking about language abstractions
- What were the 3 levels
