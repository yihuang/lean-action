# LeanAction

在 Lean 4 里表达 **action（状态迁移关系）** 并**自动化归纳不变式证明**的小型库。

* 双视图：`do` 记法书写的非确定状态 monad，与 `rel` 给出的纯关系语义，二者可互相转换；
* 模块化：`View`/`Lens` + `focus` 聚焦到嵌套结构字段；并行组合有四层——积状态
  （`interleave`）、共享状态 + **不交足迹**（`ViewModule.parallel`，框架条件
  `Disjoint` 是证明义务，附框架定理）、**rely/guarantee**（足迹相交时用接口组合）、
  **同步/同时执行**（`ViewModule.sync`）；
* 证明层：`Reach`、`Preserves`、`Hoare`、`Module`、`Refines`，**单一归纳引擎**；
* 时序层：`Always` / `Eventually` / `LeadsTo`、行为、弱/强公平性、秩论证
  （公平性下的必然性，支持"仅在不变量区域内"的变体）、交错并行的**活性组合**
  （`interleave_leadsTo`）与 `while` 终止性（`loop_can_exit`）；
  共享内存协议与并行系统的活性都有实例；
* 元编程：`deriving ViewFields, LensFields`（推荐）或 `view_defs`/`lens_defs`
  命令生成结构字段的 `View`/`Lens`（`import LeanAction.Derive`；参数化结构用命令）；
* 自动化：`action_simp` / `step` / `inv_induct` / `safe_induct`，配合 `grind` 收尾；
* **零外部依赖**（不需要 Mathlib），Lean `v4.33.0`。

设计与取舍见 [`DESIGN.md`](DESIGN.md)。

---

## 快速开始

```lean
import LeanAction
open LeanAction

structure Ctr where
  n : Nat
  log : List Nat

/-- `do` DSL：读状态、累加计数器、记录旧值 -/
def incr : Action Ctr := do
  let s ← (ActionM.get : ActionM Ctr Ctr)
  ActionM.modify fun t => { t with n := t.n + 1, log := s.n :: t.log }

def reset : Action Ctr := set { n := 0, log := [] }

def init : Nondet Ctr := fun s => s.n = 0 ∧ s.log = []
def inv  : Nondet Ctr := fun s => s.n = s.log.length
def M    : Module Ctr := ⟨init, incr <|> reset⟩

/-- 一步保持不变式 -/
theorem inv_step : Preserves (incr <|> reset) inv := by
  inv_induct
  simp only [inv, incr, reset] at *
  action_simp
  grind

/-- 安全性：所有可达状态满足 `inv` -/
theorem safe : M.Safe inv := by
  safe_induct
  · intro s hs
    unfold M at hs
    simp only [init, inv] at hs ⊢
    grind
  · inv_induct
    simp only [M, inv, incr, reset] at *
    action_simp
    grind
```

自动化模式固定为三步：**先 `simp only` 展开使用者自己的 `def`（库猜不到），
再 `action_simp` 把动作语义展开成一阶命题，最后 `grind`（或 `omega`）收尾**。

完整的可编译例子在 `Examples/`：

| 文件 | 内容 |
| --- | --- |
| `Examples/Basic.lean` | `do` DSL、`<|>`、`while` 循环、`View.comp` 嵌套字段聚焦 |
| `Examples/Parallel.lean` | `Module.interleave` 交错并行、`Refines` 精化与 stuttering |
| `Examples/Mutex.lean` | 共享变量协议：6 路进程步的互斥、构造性可达性、"被阻塞"的否定证明 |
| `Examples/Hoare.lean` | 偏正确性：`iterate`、`while`（`Hoare.loop`）、`nondet`、`focusView` |
| `Examples/DataRefinement.lean` | 非恒等抽象映射、安全性传递、实现层私有不变式、运行提升 |
| `Examples/Machine.lean` | 程序驻留状态的栈机：`choiceAll` 分派、对任意程序成立的安全性、具体运行 |
| `Examples/Liveness.lean` | 公平性下的必然性、**不公平则活性失效**的定理、`Always` 形式的互斥、循环终止性与全正确性 |
| `Examples/MutexLiveness.lean` | 共享内存协议活性：区域内（非全局单调）的 variant，"进入"与"离开"临界区两个方向，后者由安全性提供区域稳定性 |
| `Examples/ParallelLiveness.lean` | 交错并行活性：投影 + 公平性传递 + 序列级秩论证 ⇒ 乘积活性；反面例子说明分量公平不可省 |
| `Examples/Frame.lean` | 共享 record 上的不交足迹组合：框架定理（每半只在自己状态类型上证）、组合活性、同步组合、`¬ Disjoint` 说明 mutex 为何超出本层 |
| `Examples/RelyGuarantee.lean` | 足迹相交时用接口组合：每个分量只对自己的 rely/guarantee 负责 |

```bash
lake build          # 构建库 + 示例（Lean v4.33.0）
```

---

## API 速查

### 类型

| 名称 | 含义 |
| --- | --- |
| `Nondet α` | `α → Prop`，Prop 值非确定单子（`Monad` + `Alternative`） |
| `ActionM σ α` | 状态迁移 + 返回 `α`：`σ → Nondet (α × σ)` |
| `Action σ` | 纯状态迁移，notation for `ActionM σ Done` |
| `Rel α β` | `α → β → Prop`（`Rel.Comp` / `Rel.TransGen` / `Rel.ReflTransGen`） |
| `View σ α` / `Lens σ α` | 字段选取（无定律 / 带三条 lens 定律） |
| `Module σ` | `{ init : Nondet σ, next : Action σ }` |

### 动作

`skip` `fail` `guard P` `assert P` `assume P` `update f` `set v` `nondet R`
`choiceAll B`，以及组合子 `A ;; B`（`seq`）、`A <|> B`（`Alternative`）、
`A >>= f`、`iterate A n`、`while[P] A`（`loop P A`）、`liftLeft`/`liftRight`、
`focus`/`focusView`。

### 证明层

| 名称 | 含义 |
| --- | --- |
| `rel A s s'` | 动作 `A` 的迁移关系 |
| `Reach A s s'` | `rel A` 的自反传递闭包 |
| `Preserves A I` | 一步保持不变式 |
| `Hoare P A Q` | 偏正确性三元组 |
| `Module.Safe M P` | 所有可达状态满足 `P` |
| `Refines f Abs Conc` | 数据精化（允许 stuttering） |
| `Always P b` / `Eventually P b` / `LeadsTo P Q b` | 「始终 / 最终 / 一旦…就最终…」时序谓词（`b : Behavior σ := Nat → σ`） |
| `IsBehavior M b` / `IsRun M b` | `b` 是 `M` 的行为 / 从初态出发的行为 |
| `WeakFair A b` / `StrongFair A b` | 对动作 `A` 的弱/强公平性 |
| `leadsTo_zero_of_weakFair(_inv)` | 秩论证：公平性下的必然进展（`_inv` 版本只要求在不变量区域内成立） |
| `loop_can_exit` | `while` 的存在终止运行（配合 `Hoare.loop` 得全正确性） |
| `eventually_zero_of_strongFair_inv` | 强公平版本的秩论证（`StrongFair ⟹ WeakFair`） |
| `eventually_zero_of_seq` | 序列级秩论证（允许 stutter，用于投影出的行为） |
| `interleave_leadsTo` | 交错并行的活性组合（配合 `forward_stable_of_preserves`、`weakFair_fst/snd_of_weakFair`） |
| `deriving ViewFields, LensFields` | 为每个字段生成 `Struct.fView` / `Struct.fLens`（绝对命名，支持 namespace） |
| `view_defs` / `lens_defs` | 生成 `View` / `Lens`，类型以 term 给出（参数化结构用这条路径） |
| `Preserves.loop` / `Hoare.loop` | 循环的不变性 / 偏正确性 |
| `Module.interleave` + `interleave_safe` | 积状态上的交错并行及其安全性组合定理 |
| `Disjoint` + `ViewModule.parallel_safe/parallel_leadsTo` | 共享状态上按**不交足迹**组合（框架条件显式化，附框架定理） |
| `Compatible` + `Preserves.orElse_of_compatible` | 足迹相交时的 **rely/guarantee** 组合（义务只提接口） |
| `relyGuarantee_until` | 前缀稳定性（"区域保持到目标达成"），R/G 的时序孪生 |
| `ViewModule.sync` / `sync_preserves` / `sync_proj` | 同时执行（lock-step）组合子及其定理 |
| `disjoint_auto` | 自动关闭结构字段 view 的 `Disjoint` 目标 |

### 自动化

| 宏 | 用途 |
| --- | --- |
| `action_simp` | 展开动作语义（`rel_*` 引理集，`at *`） |
| `step` | `action_simp; try grind`，一条 step 义务 |
| `inv_induct` | 证明 `Preserves A I` 的标准骨架 |
| `safe_induct` / `safe_induct using I` | 证明 `M.Safe P`（可指定辅助不变式） |

---

## 仓库结构

```
LeanAction/Rel.lean      关系工具箱（Comp / TransGen / ReflTransGen + 归纳原理）
LeanAction/Nondet.lean   Prop 值非确定单子
LeanAction/Action.lean   DSL：ActionM / Action / 原语 / 组合子 / rel 语义引理
LeanAction/Lens.lean     View / Lens / focus / 积状态 lift / interleave
LeanAction/Proof.lean    Reach / Preserves / Hoare / Module / Refines
LeanAction/Tactic.lean   action_simp / step / inv_induct / safe_induct
LeanAction/Derive.lean   view_defs / lens_defs 命令（需 import Lean）
LeanAction/Frame.lean    共享状态组合：Disjoint、框架定理、ViewModule.parallel
Examples/                可编译示例
DESIGN.md                设计文档（语义决策、自动化原理、局限与路线图）
```

## 示例与探索

`Examples/` 里的 6 个文件不只是 API 演示，也是对照设计预期的实验记录：
它倒逼出的库能力（`Preserves.loop`、`Hoare.iterate/loop/nondet/update/set`、
`not_rel_guard_seq`、`interleave_safe`、`;;`）与踩到的坑（`apply` 命名隐式参数、
`rel` 到等式的 `have`、`match` 遮蔽状态变量、`decide` 对 `rel` 不可用、
`grind` 的环境敏感性、共享变量不能用 `interleave`）都记录在
[`DESIGN.md` 第 11 节](DESIGN.md#11-通过示例探索表达力与实用性)。

## 已知边界

* `Nondet` 是 `Prop` 值，**不可计算**：本库是规范/证明层，执行层需另用
  `List`/`Multiset` 单子（见 `DESIGN.md` §9.1）。
* 时序层只覆盖**秩论证型**的活性（`Always`/`Eventually`/`LeadsTo` + 弱/强公平性
  + `while` 终止性 + 共享内存协议的区间变体）；尚无不动点演算、compassion，
  不变量区域也需要人工给出（`DESIGN.md` §9.2、§11.5）。
* 并行有四种组合方式（交错 × 积/共享足迹、rely/guarantee、同步）。仍缺：rely 的
  自动发现、同步组合的活性、复杂 view 的足迹推断自动化（`DESIGN.md` §5.4、§9.3）。
* 结构字段的 `View`/`Lens` 可由 `deriving ViewFields, LensFields` 生成（推荐，
  绝对命名）；参数化结构改用 `view_defs`/`lens_defs` 命令（注意命令前不能用
  doc comment、结构需在当前 namespace 内），见 `DESIGN.md` §5.1、§11.6。
