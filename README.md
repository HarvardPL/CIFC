## CIFC

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

Object addresses are modeled as object identifers, `id`. A function `id -> option tm` is used to abstractly model stack frames. The heap is simply modeled as a list of heap objects (* garbage collections not modeled *). Heap objects are indexed using their object identifers. Contents of a heap objects are modeled as `CLASS -> FieldMap -> Label -> heapObj`.

