## Coarse-grained Information Flow Control for Java

Coq formalization of a Java-like language, including

1. semantics of the language
2. type system properties: progress and preservation
3. noninterference property

timing-sensitive noninterference (TINI) for a Java-like language. Currently compiles with version 8.7.2. 

### Language
The language is the imperative core of a Java-like language, extended with security label related expressions. This language doesn't distinginsh expression and statement, instead, it uses expressions to uniformally describe all terms. 

```
e  := x                      (* variables *) 
      | null                 (* null *)
      | True | False         (* boolean values *) 
      | e == e               (* comparing expression *)
      | e.f                  (* field access *)
      | e.meth(e)            (* method call *)
      | new cls()            (* object creation *)
      | x = e                (* assignment *)
      | x.f = e              (* field write *)
      | if e then e else e   (* if statement *)
      | e ; e                (* sequence *)
      | le                   (* label related expressions *)
      | sp_e                 (* special expressions for inner syntax *)
   
le := ℓ (* label values *)
      | labelData e ℓ        (* label operations *)
      | unlabel e            (* unlabel the target expressions *)
      | labelOf e            (* get the label of the target expressions *)
      | unlabelOpaque e      (* unlabel the opaque labeled value *)
```

Some additional expressions are used for the purpose of modeling inner structures and configurations:

```
sp_e :=  Object_identifer    (* pointers to objects *)
         | v_l e ℓ           (* runtime representation of the labeled expression *)
         | v_opa_l e ℓ       (* runtime representation of opaquely labeled expression *)
         | hole              (* evaluation context *)
         | return_hole       (* evaluation context for method calls *)
```

The details of the language are in the file [language.v](updated/language.v).

### Semantics

#### Important types

Runtime environment of valid programs comprises several essential pieces of information. We model the information using the following types:

- **Method Definition**: A method definition is composed of class name, method identifier, class for the parameters, parameter identifiers, and the body of the method: `cn -> id -> cn -> id -> tm -> method_def`. 
- **Class Definition**: A class definition is composed of class name, a list of fields, and a list of method definitions: `cn -> (list field) -> (list method_def) -> CLASS`.
- **Object Identifier**: Object addresses are modeled using a special type: object identifers `nat -> oid`. 
- **Stack Frame**: Stack frames are abstractly modeled as a function `id -> option tm`. It maps variable identifiers to their values. 
- **Heap**: 


Evaluating a valid program requires some essential pieces of information. These pieces are  of a valid program 



The heap is simply modeled as a list of heap objects (* garbage collections not modeled *). Contents of a heap objects are modeled as `CLASS -> FieldMap -> Label -> heapObj`.

A program is valid only if it has  
We defined several structures to store information. 

- class table maps from class names to their definitions: `cn -> option CLASS`. 
- 

implemented several lookup functions to retrieve contents from various places.

- 
Several lookup functions are created to retrieve contents from stack frames and heaps. 

#### Reduction

The reduction semantics of the language are documented using the small-step reduction semantics. The reduction is defined as an inductive relation: `config -> config -> Prop`. We 

### Well-formedness

#### Well-formedness of stack frames

#### Well-formedness of heap

- property 1
- property 1

### Low-equivalence


### Type system

#### Progress

#### Preservation

### Non-interference
