# Avon

![](./img/hero.jpg)

Avon is a solid-state $SKI$ interpreter runtime with accelerated supercombinator support.  It is particularly designed to evaluate [SKIjack](https://github.com/sigilante/SKIjack) and [SKIlark](https://github.com/sigilante/SKIlark) programs.

Avon supports a "solid-state" event loop, by which we mean that it has a kernel with a persistent state that can be queried and updated, using a poke and peek operation respectively.

Avon was inspired by [Urbit](https://urbit.org), [NockApp](https://github.com/nockchain/nockchain/tree/master/crates/nockapp), and [PLAN](https://github.com/sol-plunder/reaver).  The underlying $SKI$ work was originally inspired by Stephen Wolfram's [_Combinators:  A Centennial View_](https://writings.stephenwolfram.com/2020/12/combinators-a-centennial-view/).

