Coq formalisation of automated reasoning.

Files:
* requirement_page.v
  
  The tasks provided on the automated reasoning webpage as basic knowledge needed in this course.

* basic.v

  Inductive definitions, notation and coercions.

* functions.v (Loads basic.v)

  Functions like subst, pol, eval, negvar and associated definitions.

* properties.v (Loads functions.v)

  General properties needed in other proofs.

* poldef.v (Loads properties.v)

  Exercise 2.4.
  
  ![property](https://latex.codecogs.com/gif.latex?\forall&space;p~H~F~G,&space;p&space;\in&space;pos~H&space;\to&space;\\&space;(pol~H~p&space;=&space;\lfloor&space;1\rfloor&space;\to&space;eval~A~F\leq&space;eval~A~G\to&space;eval~A~hf\leq&space;eval~A~H[G]p)&space;\land&space;(pol~H~p&space;=&space;\lfloor&space;-1\rfloor&space;\to&space;eval~A~F\geq&space;eval~A~G\to&space;eval~A~hf\leq&space;eval~A~H[G]p))

* negvarProp.v (Loads properties.v)

  Exercise 3.4
  
  ![property](https://latex.codecogs.com/gif.latex?\forall&space;F,&space;\mathit{satisfiable}~F&space;\to&space;\mathit{satisfiable}&space;(\mathit{negvar}~F))

* poscomb.v

  Exercise 4.4


[//]: # "
\forall p~H~F~G, p \in pos~H \to \\ 
(pol~H~p = \lfloor 1\rfloor \to  eval~A~F\leq eval~A~G\to eval~A~hf\leq eval~A~H[G]p) \land (pol~H~p = \lfloor -1\rfloor \to eval~A~F\geq eval~A~G\to eval~A~hf\leq eval~A~H[G]p)
"
