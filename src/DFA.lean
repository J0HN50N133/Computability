import init.data.list.basic
import data.fintype.basic
/- explicit type argument -/
universes u v
/-- 按照DFA的形式化定义其五元组表示, 不过这里没有使用集合论而采用了类型论进行表示
分别为: 
输入符号类型`α`
状态类型`σ`
状态转移函数为`tansition`, `σ → α → σ`，可理解为`σ`碰到了`α`转移到新的`σ`
起始状态是`σ`的一个term
接受状态`σ`的集合 --/
structure DFA (α : Type u) (σ : Type v) :=
  (transition : σ → α → σ)
  (start : σ)
  (accept: set σ)

/- 这里定义一些DFA上的实用函数用于简化证明过程 --/
namespace DFA

/- 输入字符的类型，状态的类型，以及自动机的类型 -/
variables {α : Type u} {σ : Type v} (M: DFA α σ)

/-- 许多定理都需要假定一个类型是`inhabited`的。一个类型是`inhabited`的意味着
   它至少有一个元素。例如定理： if α is a type, ∃ x: α, x = x 为真当且仅当α是`inhabited`的。这里DFA的`inhabited`我定义为空自动机，只有一个元素，所有的转移都会回到自身（即转移函数为空），当然这需要建立在状态类型`α`也是`inhabited`的基础上，否则找不到至少一个状态。 -/
instance [inhabited σ]: inhabited (DFA α σ) :=
 ⟨ DFA.mk (λ _ _, default) default ∅ ⟩

/- `M.eval_from s input` 对从状态`s`开始读入`input`进行求值 -/
def eval_from (start : σ) (input: list α) : σ :=
  list.foldl M.transition start input

/-- 强化simp使用 -/
@[simp] lemma eval_from_nil (s:σ) : M.eval_from s [] = s := rfl
@[simp] lemma eval_from_singleton (s : σ) (a : α) : 
  M.eval_from s [a] = M.transition s a := rfl
@[simp] lemma eval_from_append_singleton (s: σ) (x: list α) (a: α):
  M.eval_from s (x++[a]) = M.transition (M.eval_from s x) a :=
  by simp only [eval_from, list.foldl_append, list.foldl_cons, list.foldl_nil]

/-- `M.eval x` evaluate `M` with input `x` starting from `M.start`-/
def eval : list α → σ := M.eval_from M.start

@[simp] lemma eval_nil : M.eval [] = M.start := rfl
@[simp] lemma eval_singleton(a:α) :
  M.eval [a] = M.transition M.start a := rfl
@[simp] lemma eval_append_singleton (x : list α) (a: α):
  M.eval (x ++ [a]) = M.transition (M.eval x) a :=
  eval_from_append_singleton _ _ _ _

lemma eval_from_of_append (start: σ) (x y: list α) :
  M.eval_from start (x ++ y) = M.eval_from (M.eval_from start x) y :=
  x.foldl_append _ _ y

end DFA
