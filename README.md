## Coarse-grained Information Flow Control for Java

This is a Coq formalization of a Java-like language, including

1. semantics of the language
2. Proof of type system properties
3. Proof of noninterference (timing-sensitive noninterference (TINI)) property

The Coq files compiles with version 8.7.2. 

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

- **Term** : The closed term to be evaluated. 
- **Frame stack** : This is the program context in which the term is currently being evaluated. Specifically, it comprises the terms that left to be evaluated in this container. 
- **Label** : This is the security label of this container. More details will be explained later. 
- **Variable state** : This variable state maps variables to their values.

Our coq file defines the container as a type: `tm -> frame_stack -> Label -> stack_frame -> container`. In this document, we use the form of `(t; fs; lb; vs)`.

#### Important types

Runtime environment of valid programs comprises several essential pieces of information. We model the information using the following types:

- **Method Definition**: A method definition is composed of a class name to which the method belongs, identifier of the method name, class names/types of the parameters, identifiers of the parameters, and body of the method: `cn -> id -> cn -> id -> tm -> method_def`. 
- **Class Definition**: A class definition is composed of a class name, a list of fields, and a list of method definitions: `cn -> (list field) -> (list method_def) -> CLASS`.
- **Class Table**: A class table maps class names to their definitions: `cn -> option CLASS`. 
- **Object Identifier**: Object addresses are modeled as a special type: object identifers `nat -> oid`. 
- **Stack Frame / Variable state**: Stack frames are abstractly modeled as a function `id -> option tm`. It maps variable identifiers to their values. 
- **Heap**: The heap is simply modeled as a list of entries of heap objects. Every heap entry comprises an object identifier that represents the address and a heap object. A heap object comprises the class definition of the object, a field function, and a security label. A field function is a partial finite map from field names to values. A security label describes the security level of the object. Heap objects are formalized as `CLASS -> FieldMap -> Label -> heapObj`.

#### Lookup functions

We also define two functions to retrieve information:

- **Lookup a heap object**: The function is used to lookup heap objects using their object identifiers: 'lookup_heap_obj (h : heap) (o : oid) : option heapObj'. 
- **Lookup a method body**: The function is used to lookup method definitions inside a class definition, using method identifiers: 'Definition find_method (cls : CLASS) (m : id)'. 

#### Configuration

We define the operational semantics in terms of transitions between configurations. Within such semantics, transition rules are defined by case analysis rather than by induction. Such semantics could simplified some proofs. 

In our formalization, a configuration can be a normal one, in error state, or in terminal state. 
```
Inductive config := 
  | Config : Class_table ->container -> list container -> heap -> config
  | Error_state : config
  | Terminal : config. 
```

A normal configuration is a four-tuple, containting the following information: 

1. **Class table**: The class table stores information of all class definitions needed. 
2. **Container being evaluated**: The container that is being executed. 
3. **Program context**: A list of containers that present the execution context. 
4. **Heap**: A list of heap objects. 

Such a tuple can be written as `(CT; ctn; ctx; H)`.

A number of expressions could lead to an error state. These are errors that are allowed at run-time as they are dynamically checked for by the Java Virtual Machine. Java's type system cannot catch these errors statically. In this formalization, we mainly concern two errors: Null-pointer exception and information flow leak. Occurances of such errors lead an execution to the error state. Some reduction rules describe such transition.  

In addition to the two kinds of configurations above, an execution can run into terminal state if it is of the form 
`(CT; (v; []; lb; vs); []; H)`. In such form, the current container has no more frames to run; the program context is empty as well. Therefore, the execution has no more terms left to be executed. 


#### Reduction

A small-step semantics is used for the reduction. The reduction is defined as an inductive relation: `config -> config -> Prop`. Details about the reduction semantics can be found the file [language.v](updated/language.v).

We define a function `hole_free` to separate closed terms and open terms. Closed terms are free of hole, and open terms are not. 

A method call leads to creation of a new execution container, and a `return hole` in the caller container. The rule below shows the formalization of a method call:
```
(* normal method call *)
| ST_MethodCall_normal : forall o h cls fields v lx sf arg_id cls_a body meth returnT ct fs ctns lb sf',
   Some (Heap_OBJ cls fields lx) = lookup_heap_obj h o -> 
   Some (m_def returnT meth cls_a arg_id body) = find_method cls meth -> 
   value v ->
   flow_to lx lb = true  ->
   sf' = sf_update empty_stack_frame arg_id v ->
   Config ct (Container (MethodCall (ObjId o) meth v) fs lb sf ) ctns h 
      ==> Config ct (Container body nil lb sf' ) ((Container (return_hole) fs lb sf ) :: ctns) h
      
```

### Well-formed configuration

To prove soundness of the semantics, we need to define well-formedness of configurations. Since a configuration is of the form `(CT; ctn; ctx; H)`, well-formedness breaks into several properties:

- Well-formedness of a heap: This is written as `CT |- H ok`. It ensures that 
  - objects in the heap are correctly addressed, and all class names mentioned in the heap are in the class table. 
  - all fields in every object are valid: the value of a field is either a valid object identifier or null. 

- Well-formedness of a container: This is written as `CT, H |- ctn ok`. For a container `(t; fs; lb; vs)`, it ensures:
  - The term `t` has valid syntax. 
  - All terms in the frame stack `fs` have valid syntax
  - The variable state is well formed. It contrains every variable to be a valid value. A valid value is one of the following: null; a valid object identifier; a labeled value; a opaquely labeled value; a label; true; and false.  
  
- Well-formedness of context containers: Every container in the program context should be a valid container. 

- The term of the container being evaluated is a close term, without hole. 

The Coq formalization of the well-formed configuration is below:
```
| valid_conf : forall ct t fs lb sf ctns h, 
    valid_ctns ct ctns h ->
    valid_ctn ct (Container t fs lb sf) h ->
    hole_free t = true ->
    wfe_heap ct h -> field_wfe_heap ct h ->
    valid_config (Config ct (Container t fs lb sf) ctns h). 
```

### Type system



#### Types

Types of this language are the following:
1. Class types: These types correspond to the classes. 
2. Bool type: This is primitive type boolean.
3. Label types: All security labels are primitive types. 
4. Labeled Types: These are parameterized types for labeled values. The type of a labeled value is parameterized by the type of the value. 
5. Opaquely labeled types: These types are similar to labeled types, but apply on opaquely labeled values. 
6. Void type: Some terms, such as assignment, are of void type. 
7. Arrow types: The type for list of terms, and list of containers are arrow types.  

#### Typing rules

The typing environment Γ is a finite partial map from variables to their types. In order to prove type soundness, the type system includes typing rules for closed terms, open terms, frame stack, container, program context, and configurations:
1. Typing rules for closed terms: `Γ, CT, H |- t : τ`. The inductive relation `tm_has_type` defines these typing rules. 
2. Typing rules for open terms: `Γ, CT, H |- t : τ -> τ`. The inductive relation `tm_hole_has_type` defines these typing rules. 
3. Typing rules for frame stack: `Γ, CT, H |- fs : τ -> τ`. The inductive relation `fs_has_type` defines these typing rules. 
4. Well-typed variable state: `Γ, CT, H |- vs ok`. Variable states map variables to their values. A variable state is well-typed if all variables in the typing environment `Γ` are in the map, and values of all variables are well-typed. 
5. Typing rules for a container: In general, the type for a container is of the form `τ' -> τ`. Types `τ'` and `τ` depend on the types of the term and the frame stack. 
6. Typing rules for program context: Program context is a list of containers. The type of a container list is of the form `τ' -> τ`.
7. Typing rules for configuration: The type of a configuration depends on the type of the container being evaluated, and the type of the program context. If the type of the container being evaluated is `void -> τ'`, and the type of the program context is `τ' -> τ`, then the type of the configuration is `τ`.

Details about the type system can be found in the file [Types.v](updated/Types.v).

#### Progress

In general, the progress theorem states that a well-typed program won't stuck. In our formalization. Progress theorem is formalized as below:

```
Theorem Progress : forall config T ct h ctn ctns, 
  config = (Config ct ctn ctns h) ->
  valid_config (Config ct ctn ctns h) ->
  config_has_type ct empty_context (Config ct ctn ctns h) T
  -> terminal_state config \/ (exists config', config ==> config').
```

The theorem says that, for a normal configuration `config`, if `config` is well-formed (valid) and well-typed, then `config` is either at terminal state, or there exists another configuration `config'` that `config` can take a step to `config'`.

Detailed proof of this theorem can be found in the file [progress.v](progress/.v).

#### Preservation

In general, preservation theorem states that reduction of a configuration preserves typing of the configuration. 

In our formalization. preservation theorem is formalized as below:

```
Theorem typing_preservation : forall T ct ctn ctns h ctn' ctns' h',
    config_has_type ct empty_context (Config ct ctn ctns h) T ->
    valid_config (Config ct  ctn ctns h) ->
    Config ct ctn ctns h
           ==> Config ct ctn' ctns' h' ->
    config_has_type ct empty_context (Config ct ctn' ctns' h') T.
```

The theorem says that, for a normal configuration `config`, if 
1. `config` is typed with T.
2. `config` is well-formed (valid).
3. `config` takes one step into `config'`
Then `config` is also typed with T. 

In order to prove this theorem, several lemmas were needed:
1. Expanding heap with a new object preserves well-formedness of configurations. 
2. Updating a heap object preserves well-formedness of configurations. 
3. Expanding heap with a new object preserves typing of configurations. 
4. Updating a heap object preserves typing of configurations. 
5. Reduction from one config to another preserve well-formedness. 

Detailed proof of the preservation theorem can be found in the file [preservation.v](updated/preservation.v).


#### Deterministic

Deterministic theorem states that reduction of a configuration is deterministic. 

In our formalization. preservation theorem is formalized as below:

```
Theorem deterministic: forall ct ctn ctns h ctn1 ctns1 h1 ctn2 ctns2 h2, 
     Config ct ctn ctns h ==>
            (Config ct ctn1 ctns1 h1)  ->
     Config ct ctn ctns h ==>
           (Config ct ctn2 ctns2 h2) ->
     ctn1 = ctn2 /\ ctns1 = ctns2 /\ h1 = h2 .
```

The theorem states that if a configuration `config` reduces to two configurations `config1` and `config2`, then `config1` is equal to `config2`. 

Detailed proof of the theorem can be found in the file [deterministic.v](updated/deterministic.v).

### Information flow security


#### Coarse-grained control

We intend to design a language and relevant features to ease enforcement of information flow policies. Compared with many fine-grained information mechianisms, our mechanism enforces information flow policies in a coarser granularity. Coarse-grained mechianism requires less effort from the users, and is still able to establish confidentiality in the target programs. Our mechanism enforces policies at the granulariy of *execution container*, the concept that we introduced above. Every execution container is responsible for running some computations. Information flow policies are enforced at the boundaries between containers.  

In this language, the concept of containers corresponds to stack frames. As described, a container is written as `(t; fs; lb; vs)`. Every container is labeled with a single label. The label floats up if the computation of the container reads more confidential information. 

#### Floating label

The label of current container floats up if its computation reads more confidential information. For example, the reduction rule below shows the field access to an object: 

```
(* normal field access *)
  | ST_fieldRead3 : forall h o fname lo lb cls F v l'  ct fs ctns sf,
      Some (Heap_OBJ cls F lo) = lookup_heap_obj h o -> 
      Some v = F(fname) -> 
      l' = join_label lo lb ->
      Config ct (Container (FieldAccess (ObjId o) fname) fs lb sf) ctns h ==> Config ct (Container v fs l' sf) ctns h 
```

The rule states that reading a field of object leads to modification of the container's label: `l' = join_label lo lb`

#### Non-sensitive upgrades

In addition to containers, every object in the heap has a security label. Objects' labels are not affected by computations in containers. Any upgrades to an object must obey information flow policies, and not change the object's label. For example, the reduction rule below shows the write access to a field of an object: 

```  
(* normal field write *)
  | ST_fieldWrite_normal : forall o h h' f lo lb cls F F' v ct fs ctns sf,
      Some (Heap_OBJ cls F lo) = lookup_heap_obj h o -> 
      F' = fields_update F f v ->
      flow_to lb lo = true ->
      h' = update_heap_obj h o (Heap_OBJ cls F' lo) ->
      (v = null \/
       (exists o' cls' F' lo', v = ObjId o' /\
                               Some (Heap_OBJ cls' F' lo') = lookup_heap_obj h o' /\
                               flow_to lo' lo = true
       )
      )->
    Config ct (Container (FieldWrite (ObjId o) f v) fs lb sf ) ctns h 
      ==> Config ct (Container Skip fs lb sf ) ctns h' 
```


The reduction rule essures that: 
1. the label of current container (`lb`) should flow to the label of the object (`lo`) being upgraded: `lb ⊑ lo`.
2. the label of the new value (`lo'`) should flow to the label of the object (`lo`) being upgraded: `lo' ⊑ lo`
3. the label of the object being upgraded is not modified. The label is still `lo`.


### Low equivalence

In order to define the low equivalence relation between two configurations, we need an approach to connect and compare the addresses allocated by two configurations. We borrow a partial bijection φ defined by [ni-formal-gc](https://github.com/MathiasVP/ni-formal-gc/blob/master/README.md). The domain (codomain) of φ is the set of object identifiers of the first (second) configuration.

#### Low equivalence of terms

We first define the low equivalence relation on terms. The relation is formalized as: 
```
Inductive L_equivalence_tm : tm -> heap -> tm -> heap ->  (bijection oid oid) ->  Prop
```
Most terms require syntactic equivalence to be low equivalence. Labeled values, opaquely labeled values, and object identifiers are special cases. 


Object identifiers are special terms because different addresses in two configurations could point to equivalent objects. Here we use the bijection φ to track the equivalence.  

For two objects both with low labels, if their object identifiers exist in the bijection φ, then they are low equivalent. 
```
| L_equivalence_tm_eq_object_L : forall o1 o2 h1 h2 cls1 F1 lb1 cls2 F2 lb2 φ, 
      left φ o1 = Some o2 ->
      Some (Heap_OBJ cls1 F1 lb1) = lookup_heap_obj h1 o1 ->
      flow_to lb1 L_Label = true ->
      Some (Heap_OBJ cls2 F2 lb2) = lookup_heap_obj h2 o2 ->
      flow_to lb2 L_Label = true ->
      L_equivalence_tm (ObjId o1) h1 (ObjId o2) h2 φ
```

Two objects are low equivalent if both of them have high label. 
```
| L_equivalence_tm_eq_object_H : forall o1 o2 h1 h2 cls1 cls2 F1 lb1 F2 lb2 φ, 
      Some (Heap_OBJ cls1 F1 lb1) = lookup_heap_obj h1 o1 ->
      flow_to lb1 L_Label = false  ->
      Some (Heap_OBJ cls2 F2 lb2) = lookup_heap_obj h2 o2 ->
      flow_to lb2 L_Label = false  ->
      L_equivalence_tm (ObjId o1) h1 (ObjId o2) h2 φ 
```

Labeled values and opaquely labeled values are similarly with respect to low equivalence. Take labeled values as an example, two labeled values are low equivalent under two circumstances:
1. Both labeled values have low label; and their values are low equivalent:
```
| L_equivalence_tm_eq_v_l_L : forall lb e1 e2 h1 h2 φ, 
      flow_to lb L_Label = true ->
      L_equivalence_tm e1 h1 e2 h2 φ->
      value e1 -> value e2 ->
      L_equivalence_tm (v_l e1 lb) h1 (v_l e2 lb) h2 φ
```
2. Both labeled values do not flow to low label:
```
  | L_equivalence_tm_eq_v_l_H : forall e1 e2 l1 l2 h1 h2 φ, 
      flow_to l1 L_Label = false ->
      flow_to l2 L_Label = false ->
       value e1 -> value e2 ->
      L_equivalence_tm (v_l e1 l1) h1 (v_l e2 l2) h2 φ
```

#### Low equivalence of stack frames

Two stack frames are low equivalent if either both stack frames are empty or values of the same variable in both stack frames are low equivalent. 

```
 L_equivalence_store_L : forall  sf1 sf2 h1 h2  φ ,
    (forall v1 v2 x,
    sf1 x = Some v1 ->
    value v1 ->
    sf2 x = Some v2 ->
    value v2 -> 
    L_equivalence_tm v1 h1 v2 h2  φ ) /\
    (sf1 = empty_stack_frame <-> sf2 = empty_stack_frame) ->
    L_equivalence_store sf1 h1 sf2 h2 φ.
```


#### Low equivalence of heaps

Two heaps are low equivalent if

- The relation φ only contains low object identifiers
- Low object identifiers related by φ are heap-value low-equivalent.

```
Inductive L_equivalence_heap : heap -> heap ->  (bijection oid oid ) -> Prop :=
  | L_eq_heap : forall h1 h2 φ ,
      (forall o1 o2, left φ o1 = Some o2 ->
                     L_equivalence_object o1 h1 o2 h2 φ) ->
      (forall o, lookup_heap_obj h1 o = None ->
                 left φ o = None) ->
       (forall o, lookup_heap_obj h2 o = None ->
                 right φ o = None) ->
      (forall o cls F lb, lookup_heap_obj h1 o = Some (Heap_OBJ cls F lb)->
                 flow_to lb L_Label = false ->
                 left φ o = None) ->
      (forall o cls F lb, lookup_heap_obj h2 o = Some (Heap_OBJ cls F lb)->
                 flow_to lb L_Label = false ->
                 right φ o = None) ->
                              L_equivalence_heap h1 h2 φ.
```

#### Low equivalence of containers

Two containers are low equivalent if 

- They are both low containers.
- Their terms are low equivalent
- Their frame stacks are low equivalent
- Their variable states are low equivalent


#### Low equivalence of program context

Program context of a configuration is a list of containers. Two program contexts are low equivalent if 

- They are both empty, or
- Containers at the same position of the program context are low equivalent

#### Low equivalence of configurations

Two configurations are low equivalent under two circumstances:

1. The top containers of both configurations are low containers, and they are low equivalent; or
2. The top containers of both configurations are high containers, and their *low component* are low equivalent. 

Here, we introduce the concept of *low component*. Intuitively, the low component of a configuration is part of program context that are only low containers. It is similar to the *erasure* function used in LIO. Low equivalence of two configurations is formalized as: 

```
Inductive L_equivalence_config : config -> config -> (bijection oid oid ) -> Prop :=
  | L_equivalence_config_L : forall ct t1 fs1 lb1 lb2 sf1 t2 fs2 sf2 ctns1 ctns2 h1 h2 φ, 
      flow_to lb1 L_Label = true ->
      flow_to lb2 L_Label = true ->
      L_eq_container  (Container t1 fs1 lb1 sf1) h1 (Container t2 fs2 lb2 sf2) h2 φ->
      L_eq_ctns ctns1 h1 ctns2 h2 φ ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1) (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)  φ
  | L_equivalence_config_H : forall ct t1 fs1 lb1 sf1 t2 fs2 lb2 sf2 ctns1 ctns2 h1 h2  φ, 
      flow_to lb1 L_Label = false ->
      flow_to lb2 L_Label = false ->
       L_equivalence_config (low_component ct (Container t1 fs1 lb1 sf1) ctns1 h1)
      (low_component ct (Container t2 fs2 lb2 sf2) ctns2 h2) φ  ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1) (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)  φ.  
Hint Constructors L_equivalence_config.
```

Details about low equivalence can be found in the file [Low_eq.v](updated/Low_eq.v).

### Timing insensitive non-interference

In order to prove the non-interference, we define a new reduction, named *p-reduction*, by merging two executions into one. P-reduction is defined as an inductive relation between two pairs of configurations:
```
Inductive parallel_reduction : config -> config -> config -> config -> Prop :=
```
Intuitively, a p-reduction transits a pair of configurations to another pair of configuration: `<conf1, conf2> =p=> <conf1', conf2'>`. The transition proceeds using the following rules:

- If the top containers of both configurations are low containers, then both configurations take one step reduction.
- If conf1 already terminates, then conf2 takes one small-step reduction.
- If conf1 is able to take one step, say to conf1', then the p-reduction depends on the label of conf1':
  - if conf1' is a high configuration, then conf1 steps to conf1', and no step for conf2;
  - if conf1' is a low configuration, which means conf1 jumps from high configuration to low configuration, then conf2 proceeds using the two following rules:
    -- if 
  
  and the resulted configuration is also H configuration

Configuration conf1 belongs to execution one; configurations conf2 and conf2' belong to execution two. 

Intuitively, for configurations conf1 and conf2, p-reduction either 




- configuration 

For example, terminating execution #1 takes steps to reduce conf1 to terminal 






