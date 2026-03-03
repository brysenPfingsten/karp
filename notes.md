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
