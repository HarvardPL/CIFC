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

### Coarse-grained information flow control

Compared with many fine-grained information mechianisms, our mechanism enforces information flow policies in a coarser granularity. We argue that our coarse-grained mechianism requires less effort from the users, and still is able to establish confidentiality in the target programs. Our mechanism also 

#### Execution container




In many information flow control mechanisms, information flow labels can be associated with variables, function signatures, and other program elements. Such mechanisms provide user with a fine-grained manipulation over annotating program elements. However, fine-grained control often leads to  
The concept of *execution container* is a key component of our language. 


### Configuration

We model the configuration of a program 


### Semantics

#### Important types

Runtime environment of valid programs comprises several essential pieces of information. We model the information using the following types:

- **Method Definition**: A method definition is composed of a class name to which the method belongs, identifier of the method name, class names/types of the parameters, identifiers of the parameters, and body of the method: `cn -> id -> cn -> id -> tm -> method_def`. 
- **Class Definition**: A class definition is composed of a class name, a list of fields, and a list of method definitions: `cn -> (list field) -> (list method_def) -> CLASS`.
- **Class Table**: A class table maps class names to their definitions: `cn -> option CLASS`. 
- **Object Identifier**: Object addresses are modeled as a special type: object identifers `nat -> oid`. 
- **Stack Frame**: Stack frames are abstractly modeled as a function `id -> option tm`. It maps variable identifiers to their values. 
- **Heap**: The heap is simply modeled as a list of entries of heap objects. Every heap entry comprises an object identifier that represents the address and a heap object. A heap object comprises the class definition of the object,  as `CLASS -> FieldMap -> Label -> heapObj`.

#### Lookup functions

We implemented two functions to retrieve information:

- **Lookup a heap object**: The function is used to lookup heap objects using their object identifiers: 'lookup_heap_obj (h : heap) (o : oid) : option heapObj'. 
- **Lookup a method body**: The function is used to lookup method definitions inside a class definition, using method identifiers: 'Definition find_method (cls : CLASS) (m : id)'. 


#### Reduction

A small-step semantics is used for the reduction. The reduction is defined as an inductive relation: `config -> config -> Prop`. Evaluation context

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
