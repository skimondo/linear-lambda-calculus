# Comparison between Beluga and Coq Implementations

## Differences

The same naming convection will be used, however some exceptions will be made to accommodate the differences between the two proof assistants.

Here's a list of major differences :

- **Modules**: TODO

Here's a list of minor differences :

- **Predefined Types**: Coq includes predefined types, such as `nat`, which may have subtle differences from our target Beluga definitions. To maintain a direct translation from Beluga without relying on Coq's predefined `nat`, we rename `nat` to `nat_alt` in the Coq implementation.

- **Overshadowing**: Coq allows overshadowing of definitions, however, to avoid confusion, especially for those familiar with Coq's standard library, alternative names will be used. For example, instead of redefining `lt`, we use `lt_alt` to represent the less-than relation for our custom natural number type, `nat_alt`.

- **Slashes in Names**: Coq does not allow slashes in names, so we replace them with underscores. For example, `lt/z` becomes `lt_z`

- **Dashes in Names**: Coq does not allow dashes in names, so we replace them with underscores and add `_cons` as a suffix. For example, `lt-z` becomes `lt_z_cons`. The `_cons` suffix is used to differentiate between the constructor and the inductive type, for example, `is_suc` is the inductive type and `is_suc_cons` is the constructor.
<!-- 
- **Automatic-Proposition-Inductives**: Coq has a flag called `Automatic-Proposition-Inductives` which is set to `true` by default. This flag automatically generates inductive propositions for inductive types. To maintain a direct translation from Beluga, we set this flag to `false` in the Coq implementation when necessary. [source](https://coq.inria.fr/doc/V8.20.0/refman/language/core/inductive.html#coq:flag.Automatic-Proposition-Inductives), Automatic Prop lowering -->
