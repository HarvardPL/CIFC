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

### Operational Semantics

#### Execution container

In Java-like languages, the stack frame plays an important role for program execution. Stack frames change as the program executes. An execution starts with the main method call. Inside the body of the main method, more method calls can be made. Whenever a method call is made, a new stack frame is created. The created stack frame contains mapping from variables relevant to the call to their values. Executing the method call will modify contents of the mapping, and probably contents of the heap. 

In this language, we use an abstract concept, *execution container*, to model the status of program execution. Every container records information that corresponds to the execution status of a method call and its stack frame. In our formalization, a container consists:

- **The term being evaluated** : This is the term that is being evaluated. 
- **Frame stack** : This is the program context in which the term is currently being evaluated. Specifically, it comprises the terms that left to be evaluated in this container. 
- **Label** : This is the security label of this container. More details will be explained later. 
- **Variable state** : This variable state maps variables to their values.

Our coq file defines the container as a type: `tm -> frame_stack -> Label -> stack_frame -> container`. 



#### Configuration

We define the operational semantics in terms of transitions between configurations. Within such semantics, transition rules are defined by case analysis rather than by induction. Such semantics could simplified 


As the reader will see this style of
semantics has the advantage that the transition rules are dened by case analysis rather than
by induction, which simplies some proofs.
A conguration is a four-tuple, containing the following information:
1. Heap: A nite partial function that maps oids to heap objects, where a heap object is
a pair of a class name and a eld function. A eld function is a partial nite map from
eld names to values.
2. Variable Stack: This essentially maps variable names to oids. To handle static blockstructured
scoping it is implemented as a list of lists of partial functions from variables to
values. (This is explained in more detail later.) We use  to denote stack concatenation.
3. Term: The closed frame to be evaluated.
4. Frame stack: This is essentially the program context in which the term is currently
being evaluated.



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


### Coarse-grained control

Compared with many fine-grained information mechianisms, our mechanism enforces information flow policies in a coarser granularity. Coarse-grained mechianism requires less effort from the users, and is still able to establish confidentiality in the target programs. Our mechanism enforces policies at the granulariy of *execution container*. Every execution container is responsible for running some computations. Information flow policies are enforced at the boundaries between containers. 





In our mechanism, the concept of containers corresponds to stack frames. 

In our design, every container is labeled with a single label. This label protects everything inside the container. The label of a container floats up if the container reads information that is more confidential than the current label. 


### Configuration

We model the configuration of a program 





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
