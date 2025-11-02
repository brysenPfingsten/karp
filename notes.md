The clauses are arbitrary ordered b/c they are converted to racket sets (or really hashes mapping to true (there's some other function like dp-list-list->set that maps some elements to false))
They are printed nicely because there's a custom write procedure

We're not eating clauses. Highlight the clause as the clique is being formed then grey it out once it is done.
