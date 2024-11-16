# Comparison between Beluga and Coq Implementations

## Differences

The same naming convection will be used, however some exceptions will be made to accommodate the differences between the two proof assistants.

Here's a list of differences :

- **Lemmas**: Beluga relies on recursive function definitions (rec) to drive the proof logic, Coq uses a rich set of tactics to guide proofs, making proof development more interactive and adaptable
Here's a list of minor differences :

- **Predefined Types**: We utilize Coq's nat from the PeanoNat library directly, avoiding the need to reimplement nat as was done in Beluga.

- **Overshadowing**: Coq allows overshadowing of definitions, however, to avoid confusion, especially for those familiar with Coq's standard library, alternative names will be used. For example, instead of redefining `lt`, we use `lt_alt` to represent the less-than relation for our custom natural number type, `nat_alt`.

- **Slashes in Names**: Coq does not allow slashes in names, so we replace them with underscores. For example, `lt/z` becomes `lt_z`

- **Dashes in Names**: Coq does not allow dashes in names, so we replace them with underscores and add `_cons` as a suffix. For example, `lt-z` becomes `lt_z_cons`. The `_cons` suffix is used to differentiate between the constructor and the inductive type, for example, `is_suc` is the inductive type and `is_suc_cons` is the constructor.
