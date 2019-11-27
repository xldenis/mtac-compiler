# TODO

- Implement interpreter
	- [x] Implement print
	- [ ] Implement ret
	- [ ] Implement bind
	- [ ] Implement unify
- Simplify string handling code
	- Seems bizarre that we'd have to implement a whole coq string to ocaml string ffi api...
- Figure out how to refine the goal state... how would I implement idtac?
- Do I need to apply a tactic to the goal internally?
- Do i need to define a goal type?
- Can I represent existential variables like free ones?
