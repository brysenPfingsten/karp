# Highlight new things added to viz
We're not eating clauses. Highlight the clause as the clique is being formed then grey it out once it is done.

# Make nodes and edges not bounce around after stepping
2 Choices
1. Draw whole graph white then make them black as they appear
2. Draw whole graph, remember coordinates, use those coordinates when they appear

# For/pairs (duplicate and not duplicate)
Something like
```racket
for/pairs [(C1 #:index i) (C2 #:index j) ∈ (clauses-of (φ a-3sat-inst))]
```

which expands to 
```racket
  for [(C1 #:index i) ∈ (clauses-of (φ a-3sat-inst))]
  for [(C2 #:index j) ∈ (clauses-of (φ a-3sat-inst))]
  if (> i j)
```
