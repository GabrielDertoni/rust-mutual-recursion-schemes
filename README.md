# Mutual Recursion Schemes in Rust

An example of how one might implement a mutually recursive AST in Rust. Currently Rust has several
limitations on it's type system which makes this hard and very verbose. However, I was also
surprised with just how much it's actually possible with the features Rust already has!

## But why?

Mostly for fun because I just thing recursion schemes are really cool. But it's also a way to
abstract await the recursion from a type. Because AST types are usually recursive, it's usually
necessary to allocate nodes on the heap. But by using recursion schemes we can actually abstract
away the way in which those nodes are stored. For example, they could be on the heap, or on some
arena allocator that allocates nodes with non `'static` lifetimes. On top of that, we get the ability
to traverse the tree with catamorphisms. This is an alternative to the visitor pattern that focuses
on a bottom up approach rather then top down. In order to send data down the tree, functional
languages usually use a closure, but in Rust that wouldn't be ergonomic and potentially costly.


## Higher kinded types

Using Rust's GATs, we can get pretty close to higher kinded types. In order to simulate them, we
define a couple traits like

```rust
trait AstNode {
    type TyCons<'ast, N: AstTy>;
}
```

Which represents that `Self` is supposed to be higher kinded. The `TyCons` GAT represents the type
constructor of `Self`. However, if self has two generic parameters (lifetime and type), we still
need something to put in the actual `impl`. For that we use `'static` for lifetimes and `TyParam`
for types. This way, whenever `TyParam` appears, we know it's just a placeholder saying the type
is higher kinded and has a parameter in that place.

```rust
impl AstNode for StmtF<'static, TyParam> {
//                     ^^^^^^^^^^^^^^^^~~~ just placeholders
    // Will always use this in order to generically construct `Self` types.
    type TyCons<'ast, N: AstTy> = StmtF<'ast, AstTy>;
}
```

because we constantly need to use `TyCons` to construct types, there is a type alias for that

```rust
type App<'ast, F, X> = <F as AstTy>::TyCons<'ast, X>;
type NApp<'ast, F, X> = <F as AstNode>::TyCons<'ast, X>;
```

so, when there is `App<'ast, F, X<'static, TyParam>>` we know it is the spiritual equivalent to
`F<'ast, X>` (we can't do this directly since `X` needs to have it's type parameters saturated and
`F` must have kind type, but we want to refer to the version of `F` without any type parameters).
