# LeanAction 设计文档

> 目标：在 Lean 4 中提供一套 DSL，用来**表达 action（状态迁移关系）**，并让**归纳不变式证明**尽可能自动化。

本文记录的是**已在 `lake build` 下通过验证**的原型（Lean `v4.33.0`，零外部依赖）的设计理由，
而不是一个纸面提案。所有代码片段都取自仓库中真实编译的文件。

---

## 1. 设计来源与取舍起点

设计最初来自一次关于 "Lean4 表达 action（状态迁移）的 DSL" 的讨论，其中给出的候选骨架是：

| 候选 | 优点 | 问题 |
| --- | --- | --- |
| `Action σ := σ → σ → Prop`（纯关系） | 最贴近语义、universe 干净 | 丢掉 `do` 记法与 monad 组合子 |
| `Action σ := Set (σ × σ)` | 复用 Mathlib 的 `Set` API | 与关系视角隔一层；不可计算 |
| `ActionM σ α := StateT σ Set α` | 直接得到 `do`/`<|>`/`get`/`set` | 依赖 Mathlib 的 `Set` monad；`Unit` 与状态不在同一 universe，`Action σ := ActionM σ Unit` 会 universe 报错 |

本库最终采取的是**双视图**：以**关系**为语义真身，以**非确定状态 monad** 为书写层。
下一节解释为什么这样做，以及为此付出的两个工程代价（`Done` 与 `Action` 的 notation）。

---

## 2. 分层架构

```
LeanAction/Rel.lean      关系工具箱：Rel、Comp、TransGen、ReflTransGen + 归纳原理
LeanAction/Nondet.lean   Nondet α := α → Prop，带 Monad/Alternative/Membership 实例
LeanAction/Action.lean   DSL 核心：ActionM、Action、原语、组合子、rel 语义引理
LeanAction/Lens.lean     模块化：Lens、View、focus、积状态 lift、交错并行
LeanAction/Proof.lean    证明层：Reach、Preserves、Hoare、Module、Refines
LeanAction/Tactic.lean   自动化：action_simp、step、inv_induct、safe_induct
LeanAction/Liveness.lean 时序层：Always / Eventually / LeadsTo、行为、公平性、秩论证
LeanAction/Derive.lean   元编程：view_defs / lens_defs 命令（结构字段的 View/Lens 生成）
LeanAction/Frame.lean    共享状态组合：Disjoint（框架条件）、框架定理、ViewModule.parallel
Examples/                计数器、嵌套结构、while、交错并行、精化
```

依赖方向严格单向：`Rel → Nondet → Action → Lens → Proof → Tactic`。
**没有 Mathlib 依赖**（原因见 §8）。

---

## 3. 核心语义决策

### 3.1 非确定性是 Prop 值单子

```lean
abbrev Nondet (α : Type u) : Type u := α → Prop
```

* `pure a := fun b => b = a`
* `s >>= f := fun b => ∃ a, s a ∧ f a b`
* `s <|> t := fun a => s a ∨ t a`，`failure := fun _ => False`

这是经典的 **angelic nondeterminism**：`s a` 读作"`a` 是可能的结果"，`>>=` 是
"所有分支的并"，`<|>` 是析取。因为它是 `Prop` 值的，库天然是**规范层**而不是执行层
（执行层的讨论见 §9.1）。

第一个工程细节：Lean 4.33 的 `Alternative.orElse` 是**惰性**的
(`f α → (Unit → f α) → f α`)，因此实例必须写成 `fun s t => union s (t ())`；
`Applicative`/`Monad`/`Alternative` 三处都要**显式给出全部字段**，否则 `pure`
会在实例自身的默认值解析中绕回自己（这是实际踩到的坑）。

### 3.2 `ActionM σ α := σ → Nondet (α × σ)`

为什么不直接用 `StateT σ Nondet α`？因为 `StateT` 就是
`σ → m (α × σ)`，而 Lean 的 `StateT`/`Monad` 都要求 **`α` 与 `σ` 落在同一个 universe**。
`Unit : Type 0`，所以 `StateT σ Nondet Unit` 只有在 `σ : Type 0` 时合法，
这会把状态类型锁死在 `Type 0`。

因此本库直接把这个类型写出来（definitionally 与 `StateT` 相同），并把 monad
实例显式挂在 `ActionM σ` 上（`Monad` + `Alternative`，全部字段显式）。这样：

* 状态 `σ : Type u` 与返回类型 `α : Type u` 同 universe，`Monad`/`Alternative` 可用；
* `do` 记法、`<|>`、`get`/`write`/`modify`/`read` 全部免费获得；
* 无需任何 Mathlib 依赖。

### 3.3 `Done`：语句的返回类型

纯状态迁移的返回类型需要一个**位于 `Type u` 的单点类型**。
`ULift.{u,0} Unit : Type (u+1)`、`PUnit.{u} : Type (u+1)` 都差一级 universe，
于是库内定义：

```lean
inductive Done : Type u where
  | mk

instance : Subsingleton Done := ⟨fun a b => by cases a; cases b; rfl⟩
@[simp] theorem eq_iff_true (d e : Done) : (d = e) = True := ...
```

`Done.eq_iff_true` 以及 `rel_bind_action`（见 §4.3）专门用来把 `Done` 从
`do` 块产生的存在量词中消掉，使自动化看到的是干净的 `∃ t, rel A s t ∧ rel B t s'`。

### 3.4 `Action` 是 notation，不是 abbrev

```lean
notation "Action" σ:max => ActionM σ Done
```

这是被 `do`-elaborator 逼出来的决定：若写成
`abbrev Action σ := ActionM σ Done`，那么面对期望类型 `Action Nat`，
Lean 的 `do` 块会先把 monad 变量定成**未应用的** `Action`，然后去合成
`Pure Action`——实例是挂在 `ActionM σ` 上的，于是失败。

改成 notation 后，`Action Nat` 在 elaboration 之前就展开成 `ActionM Nat Done`，
`ActionM` 始终是头常量，实例合成正常。代价是不能再写 `Action.rel` 这样的命名空间
（`Action` 成了关键字），所以库内所有定义直接放在 `namespace LeanAction` 下，
使用者 `open LeanAction` 后用 `rel`、`skip`、`Preserves` 等裸名。

### 3.5 关系视图 `rel`

```lean
def rel (A : Action σ) : Rel σ σ := fun s s' => A s (Done.mk, s')
```

`rel` 是**唯一**把两个视图连起来的桥，并且是**完备的**：

```lean
theorem ext {A B : Action σ} (h : ∀ s s', rel A s s' ↔ rel B s s') : A = B
theorem ofRel_rel (A : Action σ) : ofRel (rel A) = A
```

证明层只谈论 `rel`，因此规范可以自由地换写成 `do` 块或关系式，而证明不受影响。

---

## 4. DSL

### 4.1 原语

| 记号 | 语义（`rel`） | 说明 |
| --- | --- | --- |
| `skip` | `s' = s` | 空动作 |
| `fail` / `failure` | `False` | 死锁 |
| `guard P` / `assert P` / `assume P` | `P s ∧ s' = s` | 前置条件 |
| `update f` | `s' = f s` | 状态更新 |
| `set v` | `s' = v` | 整体赋新状态 |
| `nondet R` | `R s s'` | 由关系给出的任意迁移 |
| `choiceAll B` | `∃ i, rel (B i) s s'` | 一族动作的任选 |

### 4.2 组合子

| 记号 | 语义（`rel`） |
| --- | --- |
| `A <|> B`（`Alternative`） | `rel A s s' ∨ rel B s s'` |
| `seq A B` / `A >>= f` | `∃ t, rel A s t ∧ rel B t s'` |
| `iterate A n` | `n` 次 `A` 的复合 |
| `while[P] A` / `loop P A` | `(P ∧ A)^* ; ¬P`，即 `ReflTransGen` + 终止条件 |
| `liftLeft A` / `liftRight B` | 积状态上的单分量动作 |

`<|>` 直接复用 Lean 的 `Alternative` 记法，`;`/`do` 复用 monad 的 bind——
这正符合"尽量复用现有结构与符号"的目标。

### 4.3 `do` 记法

```lean
def incr : Action Ctr := do
  let s ← (ActionM.get : ActionM Ctr Ctr)
  ActionM.modify fun t => { t with n := t.n + 1, log := s.n :: t.log }
```

`get`/`read`/`write`/`modify` 定义在 `ActionM` 命名空间并 `export` 到
`LeanAction`。语义引理 `rel_bind`（一般情形）与 `rel_bind_action`（语句到语句）
让 `simp` 能把 `do` 块直接化成 `∃` 形式；`action_simp` 中把
`rel_bind_action` 排在 `rel_bind` **之前**，以保证 `do A; B` 得到
`∃ t, rel A s t ∧ rel B t s'` 这一最自然的形状。

### 4.4 `rel_*` 引理集 = 语义归一化

所有 `rel_skip`、`rel_seq`、`rel_orElse`、`rel_focus` … 都是 `@[simp]`，且
**右端不再出现 `rel`**。因此 `simp`/`grind` 能保证把任意复合 action
归约成一阶的状态命题并停机。这是全部自动化的地基；除此之外没有任何
自定义 rewrite 引擎。

---

## 5. 模块化

### 5.1 `View`（无定律）与 `Lens`（有定律）

嵌套结构的状态需要"聚焦到某个字段"的能力。库提供两层：

```lean
structure View (σ α : Type u) where   -- 无定律，一行即可构造
  get : σ → α
  set : σ → α → σ

structure Lens (σ α : Type u) where   -- get/set + 三条 lens 定律
  get : σ → α
  set : σ → α → σ
  get_set : ∀ s a, get (set s a) = a
  set_get : ∀ s, set s (get s) = s
  set_set : ∀ s a b, set (set s a) b = set s b
```

* `focusView v A`：把 `A : Action α` 提升到 `Action σ`，`rel_focusView` 是
  **`Iff.rfl`-级别**的展开，不需要任何定律；
* `Lens.comp`、`View.comp`：嵌套字段（`Outer → Inner → Nat`）；
* `Lens.fst`/`Lens.snd`、`View.fst`/`View.snd`：积状态分量。

为什么两层？因为三条 lens 定律是**证明负担**。真正需要定律的地方只有
"聚焦不再改动其它字段"这一类推理（`rel_focus'`），而**定义**聚焦动作并不需要。
把定律与定义解耦，使用者写 `View` 一行搞定，需要更强推理时再升级到 `Lens`。

**自动生成**（`LeanAction/Derive.lean`）有两条路径：

1. **`deriving ViewFields, LensFields`**（推荐）：为每个字段生成
   `Struct.fView : View Struct α` 与 `Struct.fLens : Lens Struct α`
   （三条 lens 定律由结构 eta 的 `rfl` 关闭）。走 `deriving` 机制
   （标记类 + `Lean.Elab.registerDerivingHandler`），因此：
   * 声明名是**绝对**的（`Deep.Point.xLens`），namespace 内也正确；
   * **不受 doc comment 限制**（`deriving` 子句是结构声明的一部分）。
   代价是**不支持带参数的结构**：框架用 `Deriving.mkHeader` 生成的参数绑定名带
   hygiene 后缀，无法写进 getter/setter 字符串，因此 handler 显式报错并指向命令路径。
2. **`view_defs T` / `lens_defs T`**：类型以 **term** 给出，所以参数化结构也能用
   （在 `section` + `variable (α : Type)` 里写 `view_defs (Box α)`）。
   实现方式是 command：getter/setter 从字符串 `"fun s : Box α => s.val"` /
   `"fun s v => { s with val := v }"` 经 `Parser.runParserCategory` 解析成
   **良构的 `structInstLVal` 节点**，再 `elabCommand` 发出 `def`。

之所以不写成 term 宏，见 §11.6：`{ s with f := v }` 的字段位置属于
`Lean.Parser.Term.structInstLVal` 节点，term 宏无法用 `ident` 反引用拼出来
（宏定义处能过，**使用处**才报 `unexpected syntax`）。

command 路径的两个使用注意（都由实现细节决定，也写在 `Derive.lean` 的文档里）：
* 自定义 command **前面不能放 doc comment**（`/-- … -/` 只挂到声明类命令上），
  要用普通注释 `/- … -/`；
* 结构必须位于当前 namespace 或其子 namespace 内，因为 `elabCommand` 会给声明名
  加上当前 namespace 前缀（否则会落到 `Ns.Ns.Struct.fView`）。

### 5.2 积状态与交错并行

```lean
def Module.interleave (M : Module σ) (N : Module τ) : Module (σ × τ) where
  init := fun p => M.init p.1 ∧ N.init p.2
  next := liftLeft M.next <|> liftRight N.next
```

异步（交错）并行的标准编码：状态取积，每步要么推进左分量、要么推进右分量。
`liftLeft`/`liftRight` 的语义引理把"另一分量不变"直接写进 `rel`，所以
交错并行的 step 义务仍然是一阶的（见 `Examples/Parallel.lean` 的
`twoCounters_inv_step`）。

### 5.3 精化

```lean
def Simulates (R : Rel σ_a σ_c) (Abs : Module σ_a) (Conc : Module σ_c) : Prop :=
  (∀ c, Conc.init c → ∃ a, Abs.init a ∧ R a c) ∧
  (∀ a c, R a c → ∀ c' , rel Conc.next c c' →
      ∃ a', Rel.ReflTransGen (rel Abs.next) a a' ∧ R a' c')

def Refines (f : σ_c → σ_a) (Abs : Module σ_a) (Conc : Module σ_c) : Prop :=
  Simulates (fun a c => a = f c) Abs Conc
```

允许**stuttering**（抽象侧走零步或多步）。核心定理是
`Refines.reach`（模拟关系沿具体可达性提升）与 `Refines.safe`
（安全性沿精化传递）——`Examples/Parallel.lean` 演示了"实现只多了 stutter，
安全性仍从规范继承"。

---

### 5.4 共享状态：把框架条件显式化（`LeanAction/Frame.lean`）

§5.2 的 `interleave` 只在**积状态**上组合，因为那里"两个分量互不干扰"这件事被
*类型*硬化了：状态就是 `σ × τ`，一个分量的动作不可能碰到另一个。共享 record 上
没有这种便利——进程 1 写 `pc1`、进程 2 写 `pc2`，但两者都可能写 `turn`。

要重新拿到组合性，就必须把**框架条件（frame condition）**写成可证明的事实：

```lean
structure Disjoint (v₁ : View σ α) (v₂ : View σ β) : Prop where
  get_set : ∀ s a, v₂.get (v₁.set s a) = v₂.get s     -- 写 v₁ 不影响读 v₂
  set_get : ∀ s b, v₁.get (v₂.set s b) = v₁.get s
  set_set : ∀ s a b, v₁.set (v₂.set s b) a = v₂.set (v₁.set s a) b   -- 同时执行用
```

为什么是**交换律**而不是"字段名不交"：在这个抽象层没有变量名，能说的就是
"一个的效果对另一个不可见"。这一步是**证明义务**，不是约定（`Examples/Frame.lean`
里用 `cases s; rfl` 关掉）。

在它之上是本层的三条结果：

* `Disjoint.get_of_rel`：聚焦动作不动另一个投影（框架条件最常用的形态）；
* `Preserves.focusView`（只需 `get_set`，不需要完整 lens 定律）：**分量局部的不变式
  提升到共享状态**；
* `ViewModule.parallel_preserves`：**框架定理**——交错步保持不变式
  `P ∘ v₁.get ∧ Q ∘ v₂.get`，其中 `P` 只由分量 1 负责、`Q` 只由分量 2 负责，
  "另一半"由 `Disjoint` 自动传递（还有单边形式 `parallel_preserves_fst/snd`）。

由此得到共享状态系统上的安全性与活性：

```lean
theorem parallel_safe   -- 分量不变式（各自在自己的状态类型上证明）⇒ 组合系统安全
theorem parallel_leadsTo -- 分量活性 ⇒ 组合活性（配合 proj_step / weakFair_of_lift /
                         --   forward_stable_of_preserves：投影会 stutter，所以要序列级秩定理）
```

**边界是定理，不是文档**：`Examples/Frame.lean` 证明 mutex 的两个进程
**不**满足 `Disjoint`（两者都写 `turn`）：

```lean
theorem mutex_not_disjoint : ¬ Disjoint mutexP₁ mutexP₂
```

所以那个协议确实需要手写全局不变式（§11.5 的 `inv`），而下一步的自然方向是
**rely/guarantee**（允许足迹相交，用 R/G 条件代替不交性）——见 §9.3。

与 §5.2 的关系：积状态版是"框架条件被状态类型硬化"的特例，`disjoint_fst_snd`
就是 `Lens.fst`/`Lens.snd` 的不交性证明。

## 6. 证明层：只有一个归纳引擎

```lean
def Reach (A : Action σ) : Rel σ σ := Rel.ReflTransGen (rel A)

def Preserves (A : Action σ) (I : Nondet σ) : Prop :=
  ∀ s, I s → ∀ s', rel A s s' → I s'

theorem Preserves.reach (h : Preserves A I) :
    ∀ s, I s → ∀ s', Reach A s s' → I s'      -- ← 唯一的归纳
```

`Reach` 用 `ReflTransGen`（而不是 `TransGen`）是为了让"零步"情形直接落到
初始条件上。所有安全性结论都是 `Preserves.reach` 的推论：

```lean
theorem Module.safe_of_preserves (hinit : M.init ⊆ₙ P) (hstep : Preserves M.next P) : M.Safe P
theorem Module.safe_of_invariant (hinit : M.init ⊆ₙ I) (hstep : Preserves M.next I) (hIP : I ⊆ₙ P) : M.Safe P
```

Hoare 三元组 `Hoare P A Q` 也是同一套语义的另一面，并为 `skip`/`seq`/`<|>`/
`guard` 以及**聚焦**（`Hoare.focusView`：内层三元组通过 view 提升到外层）
提供了规则。

这个"单一归纳引擎 + 组合子代数"的结构，正是自动化能够保持简单的根本原因：
自动化永远只需要处理**一步**，从不接触归纳本身。

---

## 7. 自动化

### 7.1 为什么不做更重的自动化

候选做法包括：自定义 `aesop` 规则集、`@[grind]` 全量标注、或在元编程里做
符号执行。原型选择的是一条更窄但**可预测**的路线：

1. **语义归一化交给 `simp`**：`rel_*` 引理集已经是完备的展开规则（§4.4）。
2. **一阶推理交给 `grind`**：状态是普通数据结构，剩下的义务是算术/等式/析取。
3. **证明骨架交给 4 个宏**，它们只负责"摆形状"，不做搜索。

因此自动化失败时，失败点总是可解释的（"某个 def 还没展开"或"grind 推不出这条算术"）。

### 7.2 四个宏

| 宏 | 作用 |
| --- | --- |
| `action_simp` | `simp (config := {failIfUnchanged := false}) only [rel_*, ActionM.*_apply, Prod.mk.injEq, ...] at *`；把动作语义展开到一阶 |
| `step` | `action_simp; try grind`：一条 step 义务 |
| `inv_induct` | `unfold Preserves; intro s hs s' hstep; step`：`Preserves` 的标准骨架 |
| `safe_induct` | `apply Module.safe_of_preserves`，留下 `init ⊆ P` 与 `Preserves next P` 两个目标 |

两个关键实现细节：

* `failIfUnchanged := false`：`action_simp` 在"没有 `rel` 可展开"时不应报错，
  否则 `try step` 与后续手动展开会互相打架。
* macro 里**不要**用 `·` 分支：早期版本把 `·` 写在 macro 体内，导致调用处的
  `·` 与 macro 内部的目标聚焦互相抢占，出现"unsolved goals"与
  "No goals to be solved"同时报出的诡异现象。现在统一用
  `apply ... <;> try step`，目标结构留给调用者。

### 7.3 使用者的典型证明

```lean
theorem twoCounters_safe : twoCounters.Safe inv := by
  safe_induct
  · intro p hp                       -- init ⊆ inv
    simp only [twoCounters, Module.interleave, counter, inv] at hp ⊢
    omega
  · inv_induct                       -- Preserves twoCounters.next inv
    simp only [twoCounters, Module.interleave, counter, inv] at *
    action_simp
    grind
```

模式是固定的：**先展开使用者自己的 `def`（库无法猜），再 `action_simp`
展开动作语义，最后 `grind` 收尾**。`Examples/` 里的每个定理都遵循它。

---

## 8. 与 Mathlib 的关系

本库**刻意不依赖 Mathlib**，原因有三：

1. 环境约束：目标机器上 Mathlib 源码/缓存不可用，从源码构建需要数 GB 空间；
2. 该用户的其它 Lean 仓库也保持零/轻依赖；
3. 库真正需要的 Mathlib 内容很少：`Set`、`Relation.Comp/ReflTransGen`、
   `StateT`/`MonadState`。前两者在 `Rel.lean`/`Nondet.lean` 里以约 200 行复刻，
   后者用自写的 `ActionM` 实例替代。

**互操作性没有损失**：`Nondet α` 就是 `α → Prop`，而 Mathlib 的 `Set α` 也是
`α → Prop`（定义上相同）。因此一旦用户 `import Mathlib`：

* `Nondet` 的值可以直接当作 `Set` 使用，`∈`/`⊆`/`⋃` 的 Mathlib 引理可直接套；
* `Rel` 与 `Relation` 的 `Comp`/`ReflTransGen` 也是同构写法，可互相转换；
* 若愿意，也可以把 `Action σ` 通过 `rel` 映射到 `σ → Set σ`，把本库的
  `Preserves` 与 Mathlib 中任何 `Set`-based 规约工具连接起来。

真正的风险只有一个：本库自定义的 `Membership α (Nondet α)` 实例与 Mathlib 的
`Set` 实例在同一环境下可能造成 `∈` 的实例歧义。规避方式是把
`Nondet` 的成员记法限制在 scope 内，或直接使用 `s a`。

---

## 9. 局限与路线图

### 9.1 规范层 vs 执行层

`Nondet` 是 `Prop` 值，因此**不可计算**：本库不能直接运行。若需要执行：

* 用 `List`/`Multiset` 单子写可执行的 `ActionM`，再用 `List.toSet` 与
  `rel` 建立对应关系（soundness/completeness）；
* 或者只为已经确定的动作提供 `Decidable` 实例。

### 9.2 时序与活性

已实现（`LeanAction/Liveness.lean`），分两层：

* **时序谓词**：`Behavior σ := Nat → σ`、`Always P b := ∀ n, P (b n)`、
  `Eventually P b := ∃ n, P (b n)`、`LeadsTo P Q b`（任意时刻起最终），
  以及 `IsBehavior` / `IsRun`。safety 与时序的桥是 `always_of_safe`：
  `M.Safe P` + 从初态出发的行为 ⇒ `Always P b`。
* **公平性下的必然性**：`TakesStep`、`WeakFair`、`StrongFair`
  （以及 `StrongFair.toWeakFair`），加上秩论证
  `eventually_zero_of_nat_progress_from` / `eventually_zero_of_weakFair(_inv)` /
  `leadsTo_zero_of_weakFair(_inv)`：若进展动作 `A` 在目标未达时严格减小
  `μ : σ → Nat`、所有步不增大 `μ`、`A` 在 `μ > 0` 时始终可用，且行为对 `A`
  弱公平，则 `μ` 最终归零（且"从任意时刻起"成立，因而可写成 `LeadsTo`）。
  `_inv` 变体只要求在**不变式区域 `I` 内**成立，且 `I` 只在 `μ > 0` 时需要——
  共享内存协议的 variant 通常**不是全局单调的**（离开临界区会让它回升），
  这一放宽是那类证明的前提。
* **循环终止性**：`loop_can_exit` 用 variant 给出 `while` 的"存在终止运行"，
  与 `Hoare.loop`（偏正确性）组合即得循环的**全正确性**
  （见 `Examples/Liveness.lean` 的 `countTo3_total`）。

共享内存协议的活性已经有实例：`Examples/MutexLiveness.lean` 证明
"进程 1 在区域（等待且持有 turn）内、对 `enter1` 弱公平 ⇒ 最终进入临界区"，
以及互补方向"在临界区内、对 `exit1` 弱公平 ⇒ 最终离开"（后者还会**消费**
安全性：区域的稳定性来自 `Mutex.inv_step`）。做法是给 variant 配上手工区域
`Region`，而不是指望全局单调。

交错并行的活性也能组合：`interleave_leadsTo` 把"分量最终达到 `P`/`Q`"合成为
"乘积最终达到 `P ∧ Q`"，其中分量的 `Preserves` 提供**前向稳定性**
（`forward_stable_of_preserves`），公平性由 `weakFair_fst_of_weakFair` /
`weakFair_snd_of_weakFair` 从乘积传到分量（`Examples/ParallelLiveness.lean`）。

仍然没有：`Always`/`Eventually` 的不动点演算与复合规则（如 `Always (Eventually P)`）、
compassion/公平性不变式、以及**区域自动合成**——目前区域与 variant 都要人工给出
（`Region` 的"到目标前稳定"要按前缀归纳证明，因为它在全局上并不被保持）。

### 9.3 其他

* **Lens 派生**：`deriving` handler 或 `lens!` 宏（见 §5.1）。
* **并行语义**：交错语义有两层——积状态（`interleave`，§5.2）与共享状态 +
  不交足迹（`Frame.lean`，§5.4）。仍缺：(a) **rely/guarantee**（足迹相交，如 mutex
  的 `turn`）；(b) **同步/同时执行**的组合子（`Disjoint.set_set` 已经备好，但没有
  `sync` 组合子）；(c) 足迹的自动化推断（目前 `Disjoint` 要手写或 `cases s; rfl`）。
* **不变式合成**：现在需要人工给出 `inv`；`Module.safe_of_invariant` 的形状已经
  适合接入 IC3/Houdini 式的不变式猜测。
* **`grind` 依赖**：`action_simp` 的兜底是 Lean core 的 `grind`；若某处不适用，
  退回 `omega`/`simp_all`/人工 `rcases` 即可（示例中都保留了这种退路）。

---

## 10. 验证

```bash
lake build      # Lean v4.33.0，零依赖，17 个 job，无 warning
```

已通过编译的示例覆盖：

| 示例 | 覆盖内容 |
| --- | --- |
| `Examples/Basic` | `do` DSL、`<|>`、不变式 `n = log.length`、`safe_induct`、`while` + `rel_loop`、`View.comp` 嵌套字段聚焦 |
| `Examples/Parallel` | `Module.interleave` 交错并行、求和不变式、`Refines` + stuttering |
| `Examples/Mutex` | 共享变量协议（turn-based 互斥）：`guard` + 6 路进程步、混合两进程的不变式、`safe_induct`/`safe_of_invariant`、构造性可达性、`not_rel_guard_seq` 证明"被阻塞" |
| `Examples/Hoare` | 偏正确性：`Hoare.iterate`（算术后置条件）、`Hoare.loop`（while + 退出条件）、`Hoare.nondet`、`Hoare.focusView`（聚焦三元组） |
| `Examples/DataRefinement` | 非恒等抽象映射、安全性沿精化传递、实现层私有不变式（`count = log.length`）、`Refines.reach` 把具体运行提升为抽象运行 |
| `Examples/Machine` | 程序驻留状态的栈机：`choiceAll` 做指令分派、对**任意程序**成立的安全性（代码不增长）、具体运行 `[push 2, push 3, add] → [5]` |
| `Examples/Liveness` | 公平性下的必然性（计数器必达 3）、**不公平则活性失效**的显式定理（stuttering 行为）、safety→`Always` 的桥（含互斥协议的 `Always`）、`while` 终止性与循环全正确性 |
| `Examples/MutexLiveness` | 共享内存协议的活性：区域内的 variant（非全局单调）、"进入临界区"与"离开临界区"两个方向；后者由安全性（互斥不变式）提供区域稳定性 |
| `Examples/ParallelLiveness` | 交错并行的活性组合：分量活性（经投影 + 公平性传递 + 序列级秩论证）合成乘积活性，反面例子说明右分量公平假设不可省 |
| `Examples/Frame` | 共享 record 上的不交足迹组合：框架条件作为证明义务、框架定理给出组合安全性（每半只在自己的状态类型上证）、组合活性、以及 `¬ Disjoint` 说明了 mutex 为何超出本层 |

---

## 11. 通过示例探索：表达力与实用性

本节是"写例子时真实发生了什么"的记录（含踩坑），比照 §3–§7 的设计预期。

### 11.1 示例倒逼出来的库能力

| 缺口 | 新增 |
| --- | --- |
| `while` 的不变性无从下手 | `Preserves.loop`、`loop_invariant` |
| 偏正确性只覆盖 `skip/seq/guard/nondet` | `Hoare.update`、`Hoare.set`、`Hoare.iterate`、`Hoare.loop` |
| "守卫失败 ⇒ 这一步不可达"（互斥里证明另一进程被阻塞） | `not_rel_guard_seq` |
| 交错并行的安全性无法组合 | `interleave_init`、`reach_interleave_fst/snd`、`interleave_safe` |
| 顺序组合没有记法（只能写 `seq A B` 或 `do`） | `;;`（`infixl:60`，作用在 `seq` 上） |

其中 `interleave_safe` 最有价值：它是**交错并行的安全性组合定理**——
`M.Safe P` 与 `N.Safe Q` 蕴含 `(M.interleave N).Safe (P ∘ fst ∧ Q ∘ snd)`，
证明只依赖"可达性在两个投影下分别下降"（`reach_interleave_fst/snd`）。

### 11.2 顺手的地方

* **协议规模不是问题**：Mutex 的 6 路非确定步（含两条改写共享变量 `turn` 的 `exit`）
  用 `inv_induct; simp only [...]; action_simp; grind` 一次通过，不需要手工 `rcases`。
* **三段式不变式**（`init ⊆ I` → `Preserves next I` → `I ⊆ P`）与真实证明习惯吻合，
  `Module.safe_of_invariant` 直接给出这个形状。
* **构造性可达性**：`Reach.single`/`Reach.step` 链 + 每步一个 `action_simp` 引理，
  可以同时证明"什么能发生"（`p1_can_enter`）与"什么不能发生"（`p2_blocked_...`）。
* **精化与实现细节并存**：抽象层用 `Refines.safe` 拿接口性质，实现层用 `Preserves`
  证明日志长度这类抽象层看不见的性质，两者互不干扰。
* **程序驻留状态的分派**：`choiceAll` + `guard (code.head? = some i)` 让"取当前指令"
  不需要对状态做依赖模式匹配；`Instr` 只是普通归纳类型，分派靠存在量词的见证。

### 11.3 别扭之处与已做的改进

1. **`inv_induct` 曾内置 `try grind`，会静默证完整个目标**，随后用户写的
   `simp only [...]`/`grind` 立刻报 `No goals to be solved`，且很难从报错定位。
   已改为 `inv_induct = unfold Preserves; intro …; action_simp`（不调用 `grind`），
   行为可预测；需要 `grind` 的地方明确写出来。
2. **`apply L (P' := …)` 在"被指定的隐式参数不出现在结论里"时不可靠**
   （`Hoare.focusView`、`Module.safe_of_invariant` 都踩到）。改用
   `refine L (…) ?_ ?_ ?_` 或项模式；这是 Lean 的 `apply` 目标导向统一使然。
3. **把 `rel` 假设"降级"为具体等式不能靠 `have`**：`rel (update f) s s'` 与
   `s' = f s` 之间隔着 `Done`/`Prod.mk.injEq`，**不是** defeq。必须先
   `simp only [f, Module.next, rel_update] at h`，再当等式用。
4. **状态里的 `match` 分支会遮蔽同名变量**：`match m.stack with | a::b::rest => … | s => …`
   里的 `s` 让后续 `cases m.stack` 找不到 `m`。规避：把中间状态也用同名变量接住
   （`obtain ⟨m, ⟨-, rfl⟩, h⟩ := h`），或把"逐指令事实"先抽成独立引理
   （`execInstr_code_shrinks`）——后者更稳。
5. **`decide`/`native_decide` 对 `rel` 目标不可用**：`Decidable (rel A s s')` 无法合成，
   因为 `rel` 是函数、实例搜索不会展开它。具体计算改用
   `simp only [...] <;> first | rfl | grind`。
6. **`grind` 的表现对环境敏感**：Machine 例子里同样的目标，`deriving DecidableEq`
   与否会影响结果；`code_never_grows` 一次成功、后来同类目标失败，最终靠把
   算术抽成 `execInstr_code_shrinks` 引理才稳定。**结论：关键证明不要全押在
   `grind` 上，把可手工的部分（算术、列表长度）抽成引理。**
7. **共享变量并行不是 `interleave` 的适用面**：Mutex 的 `turn` 同时被两个进程读写，
   不能用"两个独立模块取积"表达，只能手写一个全局 record + 进程步的 `<|>`。
   这界定了 `interleave` 的语义：**独立分量**的异步组合；共享内存需要框架/分离层。
8. **循环的终止性仍无**：`Preserves.loop`/`Hoare.loop` 只做偏正确性；活性（fairness,
   `Eventually`）不在当前范围内（§9.2）。

### 11.4 活性层带来的额外经验

* **核心引理不能用 `Nat.find`**：`import Std` 下没有 `Nat.find/find_spec/min'`，
  也没有 `Nat.strong_induction_on`、`Nat.le_induction`。`LeanAction` 零依赖的
  约束因此把秩论证改成 **`Nat.strongRecOn` 上的良基递归**：从"当前秩 > 0"
  出发，用公平性产生一次严格下降，再对更小的秩递归（`eventually_zero_of_nat_progress_from`）。
  这反而比"取序列最小值"更短，也不需要最小元存在性的引理。
* **`by_contra` 不在 core**（属于 Mathlib）：活性的反证风格要改成
  `by_cases` + `absurd`（见 `eventually_iff_not_always_not`）。
* **公平性必须被显式否证一次**：`Examples/Liveness.stuck` 给出同一模块的
  stuttering 行为，并证明它不是弱公平的、且永不达目标
  （`liveness_needs_fairness`）。把"没有公平性就没有活性"写成定理，比在文档里
  声明更有说服力，也避免把公平性当成技术细节。
* **全正确性 = 偏正确性 + 终止性**：`Hoare.loop`（偏正确性）与
  `loop_can_exit`（存在终止运行）拼起来就是 `countTo3_total`；这条拼装关系
  验证了 proof 层与 liveness 层的接口设计。
* **`LeadsTo` 的量化顺序很关键**：`eventually_zero_of_weakFair` 的结论先做成
  `∀ n, ∃ N ≥ n, …`，再包装成 `LeadsTo`；否则只能得到"从时刻 0 出发"的弱形式。
* **状态型公平 vs 关系型公平**：库里的"taken"定义为
  `rel A (b n) (b (n+1))`（该步满足 `A` 的关系），因此对 `A <|> B`
  的模块，"`A` 一直可用但环境始终走 `B`"正好是弱公平被违反的情形——
  这也是 `stuck` 能被否证的原因。

### 11.5 共享内存协议活性的实现经验

把活性推到 `Mutex` 这样的共享变量协议时，暴露了三件事：

1. **variant 不是全局单调的**。`rank s = if s.pc1 = 2 then 0 else 1` 在"离开临界区"
   这一步会从 `0` 回到 `1`。原来的秩论证要求全局 `μ s' ≤ μ s`，因此必须放宽成
   "只在不变式区域 `I` 内、且只在 `μ > 0` 时要求单调、要求 `A` 可用"
   （`eventually_zero_of_weakFair_inv`）。这个放宽不是形式上的：`hI` 只在
   `μ > 0` 时需要，正对应"目标一旦达成，后续状态怎样都无所谓"。
2. **区域在全局上并不被保持**，所以 `Preserves`/`always_of_preserves` 用不上：
   `Region ∨ pc1 = 2` 会被 `exit1` 破坏（`pc1` 变成 `0`）。真正成立的是
   **前缀形式**："只要还没进过临界区，就一直留在区域内"，它按行为前缀归纳证明
   （`region_until_goal`），并在证明里用"下一步 `pc1 ≠ 2`"排掉 `enter1` 这一支。
   这也让 `eventually_enter1` 的证明要以 `by_cases (∃ N, pc1 = 2)` 开场：
   已达成直接收工，未达成才有"全程 `μ > 0`"从而区域成立。
3. **安全性与活性对模型的要求不同**。原来的 `Mutex` 例子把 `req1`（请求锁）写成
   无守卫的 `update (pc1 := 1)`：安全性照样成立（它不动 `turn`），但一个处于临界区的
   进程可以"重新请求"退回等待，区域因此不再稳定，活性证不出来。补上
   `guard (pc1 = 0)` 后一切顺畅。**结论：安全性宽松的建模会在活性处露馅。**

另外，互补方向 `leadsTo_exit1`（离开临界区）是活性**消费**安全性的例子：
"在临界区 ⇒ 持有 turn" 这一条来自 `Mutex.inv_step` + `always_of_preserves`，
没有它就无法排除另一进程的步骤，variant 的单调性也就证不出来。

### 11.6 生成器：term 宏为什么不行，command 为什么行

`Lens`/`View` 的自动生成绕了两次弯路，最后用 command 解决：

* **term 宏两次失败**（`lens!`、`view!`）。`{ s with f := v }` 的字段位置是
  `Lean.Parser.Term.structInstLVal` 语法节点，而 term 宏的反引用只能产出
  `ident`；把它硬塞进该位置后，**宏定义处类型检查通过**，展开结果却在**使用处**
  报 `unexpected syntax`——失败点与病因分离，极易误判。
* **command 方案**：把 getter/setter 当字符串解析
  （`Parser.runParserCategory env `term "fun s v => { s with f := v }"`），
  得到良构节点，再 `elabCommand` 发出 `def`。这条路一次就通。
* 实现里踩到两个具体坑，都写进了命令的文档：
  1. **自定义 command 前不能有 doc comment**：`/-- … -/` 只会挂到声明类命令
     （`def`/`theorem`/`structure`…）上，`/-- … -/ view_defs Foo` 直接是语法错误；
  2. **`elabCommand` 会给声明名加当前 namespace 前缀**：所以我把它生成的名字
     相对化（`Name.replacePrefix currNs anonymous`），否则会落到
     `Ns.Ns.Struct.fieldView`；结构不在当前 namespace 内时命令直接报错。
  （这两条都不是"文档型"注意事项，而是会让用户莫名其妙失败的约束，因此必须
  在命令的 docstring 里写明。）
* **`deriving` 路径**随后补上，并暴露了另外三个元编程细节：
  1. 框架 API 是 `Lean.Elab.registerDerivingHandler`（不是 `Lean.Elab.Deriving.*`），
     `DerivingHandler := Array Name → CommandElabM Bool`，返回 `true` 表示
     "已处理"，从而**不**生成默认实例；注册名必须是**完全限定**的类名
     （`LeanAction.ViewFields`），只写短名匹配不上；
  2. `deriving X` 要求 `X` 能在环境中解析，所以需要一个**标记类**
     （`class ViewFields (σ : Type u)`）——没人把它当真的类型类用，handler 里
     返回 `true` 抑制实例生成；
  3. **custom command 里的 `liftTermElabM (Term.elabType …)` 看不到 section
     variable**，所以命令不能用 `elabType` 来提取结构名（那会报
     "Unknown identifier α"，但**同时**又把 `def` 建出来，因为 `elabCommand`
     是把声明当作声明来展开的，那里 section variable 是可见的）。改成**纯语法地**
     找最左标识符 + 候选名（原样 / 当前 namespace 前缀 / 去掉 `_root_.`），
     并跳过 `anonymous` 标识符节点。

### 11.7 并行活性组合：投影会 stutter

把 `interleave_safe` 的思路搬到活性上，暴露了一个结构性差别：

* **投影不是分量模块的行为**。把乘积行为投影到第一分量，另一分量的步在该分量上
  表现为**不动**（stutter），而 `IsBehavior M` 要求每一步都由 `M.next` 关联，
  所以投影不是 `IsBehavior M`。因此模块级秩定理（`eventually_zero_of_weakFair*`）
  在这里不适用，秩论证必须下沉到**序列级**（`eventually_zero_of_seq`，只需
  "秩不增 + 公平 + 进展动作可用"这些逐点事实），模块级版本随后成为它的推论。
* **合取两个"最终"需要稳定性**。"最终 `P`"与"最终 `Q`"取较晚的时刻得到
  `P ∧ Q`，前提是 `P`/`Q` 沿行为**前向稳定**（`forward_stable_of_preserves`
  从 `Preserves` 给出）。这就是"安全性 + 活性 ⇒ 合取活性"的具体形态，也正是
  `interleave_leadsTo` 里那两个 `Preserves` 假设的用途——在例子里它们退化成
  "计数器只增不减"这种显然的目标单调性。
* **公平性沿投影传递**：`weakFair_fst_of_weakFair` / `weakFair_snd_of_weakFair`
  只需要"分量动作可用 ↔ 提升动作可用"这条对应（即 `rel_liftLeft`/`rel_liftRight`
  的展开），与 stutter 无关。
* **反面例子**：`leftOnly`（只动左分量）是乘积的合法行为、甚至对左分量的提升动作
  弱公平，却永远达不到 `p.1 ≥ 3 ∧ p.2 ≥ 4`——右分量的公平假设确实不可省。

### 11.8 框架条件显式化：经验

* **`ViewModule` 只需要 `get_set`**，不需要完整 lens 定律：框架定理只用到
  "写进视图再读回来"这一条，所以足迹比 `Lens` 更宽松（`View` + 一条定律）。
  这降低了使用门槛：用户不必证 `set_get`/`set_set` 就能用组合定理。（我一开始
  用 `Lens` 作足迹，后来发现不必要。）
* **不要给 `Lens → View` 加 `Coe` 实例**：目标类型未知时 Lean 会**静默地不插入
  coercion**，于是 `Disjoint M₁.view M₂.view` 报出的错是"`M₂.view` 是 `Lens` 但期望
  `View ?m`"——很难从字面猜到根因。改成显式 `View.ofLens`（或让足迹类型本身就是
  `View`）就干净了。
* **`parallel` 不是语法上可交换的**：`M₁ ∥ M₂` 的 `next` 是 `lift₁ <|> lift₂`，
  与 `lift₂ <|> lift₁` 只是逻辑等价。所以"把同一个泛型分量活性引理套到第二个分量
  上"需要一条小引理 `isBehavior_parallel_swap`（或者 `Module` 层面的交换律）。
  这类"语义对称、语法不对称"的地方，泛型引理的实例化总要额外交接一次。
* **Lean 的 `rw` 只做语法匹配**，在这层撞了两次同一个坑：
  1. beta-redex：目标写的是 `(fun s => P (v.get s)) s'`，`rw [h]` 找不到 `v.get s'`
     → 先用 `change P (v.get s')` 打开；
  2. 结构常量的投影：泛型引理给的是 `C₁.view.get`，而目标里已是 `fp₁.get`
     → 用 `have h' : <显式类型的等式> := h`（`have` 走 defeq，`rw` 不走）。
  最终我把示例里的活性引理写成对 `M.view` 泛型、实例化时传 `C₁`/`C₂`，就把第 2 类
  摩擦集中到了一处。
* **边界写成定理最有说服力**：`mutex_not_disjoint` 让"这个协议不能用框架组合"不再
  是一句断言，而是一个一行的反例证明——这和上一轮 `liveness_needs_fairness` 是同一
  个套路：把"做不到"形式化。

### 11.9 结论

* 表达能力上，顺序、非确定（`<|>` / `nondet` / `choiceAll`）、守卫、循环、聚焦
  （`focus`/`focusView`）、精化（含 stuttering）、交错并行、构造性可达性，都能在
  同一套 `rel` 语义下表达并证明；新示例里没有一个需要绕过 DSL 直接写
  `σ → Prop`。
* 实用性上，最有效的证明配方是：
  **`safe_induct`/`Module.safe_of_*` → `inv_induct` → `simp only [<自己的 def>] at *`
  → `action_simp` → `grind`（算术/列表推理不稳时换 `omega` 或抽引理）**。
* 主要的"自动化风险"不是覆盖不足，而是**静默过强**（`grind` 顺手证完整个目标）
  与**环境敏感**（`deriving`、simp 集顺序）。这两点在设计上应当继续用
  "可预测 > 强大"的取舍来处理。
