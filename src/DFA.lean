import init.data.list.basic
import data.fintype.basic
import tactic.norm_num
import language
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

/- `M.accepts x`能接受`x`，如果对于`x`有`M.eval x ∈ M.accept` -/
def accepts : language α :=
  λ x, M.eval x ∈ M.accept

lemma mem_accepts (x : list α) : x ∈ M.accepts ↔ M.eval_from M.start x ∈ M.accept := by refl

/- fintype说明σ是有限的类型(集合)而非无限的类型(集合) -/
lemma eval_from_split [fintype σ] {x : list α} {s t : σ}
/- card是cardinal的缩写 -/
(hlen : fintype.card σ ≤ x.length)
(hx : M.eval_from s x = t) :
∃ q a b c,
x = a ++ b ++ c ∧
a.length + b.length ≤ fintype.card σ ∧
b ≠ [] ∧
M.eval_from s a = q ∧
M.eval_from q b = q ∧
M.eval_from q c = t :=
begin
  /- 利用fintype上的鸽巢原理(鸽子和鸽巢都是有限的) -/
  /- 那么有长度n和m, n和m不等,-/
  /- 且`M.eval_from s (x.take n)` = `M.eval_from s (x.take m)`-/
  obtain ⟨n, m, hneq, heq⟩ := fintype.exists_ne_map_eq_of_card_lt
  (λ n : fin (fintype.card σ + 1), M.eval_from s (x.take n)) (by norm_num),
  /- 不失一般性，我们可以假设n≤m -/
  wlog hle : (n : ℕ) ≤ m using n m,
  /- 又已经知道n和m不等了，所以n<m -/
  have hlt : (n : ℕ) < m := (ne.le_iff_lt hneq).mp hle,
  /- m:|σ| + 1 ≤ |σ|, n < m < |σ| -/
  have hm : (m : ℕ) ≤ fintype.card σ := fin.is_le m,
  dsimp at heq,

  /- 那么q,a,b,c就都找到了, 分别是:-/
  /- q = M.eval_from s (x.take m).take n = M.eval_from s (x.take n)-/
  /- a = x.take m-/
  /- b = (x.take m).drop n-/
  /- c = x.drop m -/
  refine ⟨M.eval_from s ((x.take m).take n), (x.take m).take n, (x.take m).drop n, x.drop m,
    _, _, _, by refl, _⟩,

  { rw [list.take_append_drop, list.take_append_drop] },

  { simp only [list.length_drop, list.length_take],
    rw [min_eq_left (hm.trans hlen), min_eq_left hle, add_tsub_cancel_of_le hle],
    exact hm },

  { intro h,
    have hlen' := congr_arg list.length h,
    simp only [list.length_drop, list.length, list.length_take] at hlen',
    rw [min_eq_left, tsub_eq_zero_iff_le] at hlen',
    { apply hneq,
      apply le_antisymm,
      assumption' },
    exact hm.trans hlen, },

  have hq :
    M.eval_from (M.eval_from s ((x.take m).take n)) ((x.take m).drop n) =
      M.eval_from s ((x.take m).take n),
  { rw [list.take_take, min_eq_left hle, ←eval_from_of_append, heq, ←min_eq_left hle,
        ←list.take_take, min_eq_left hle, list.take_append_drop] },

  use hq,
  rwa [←hq, ←eval_from_of_append, ←eval_from_of_append, ←list.append_assoc, list.take_append_drop,
       list.take_append_drop]
end

/- x绕回来了,多用几个x多绕几圈或者不绕 -/
lemma eval_from_of_pow {x y : list α} {s : σ} (hx : M.eval_from s x = s)
  (hy : y ∈ @language.star α {x}) : M.eval_from s y = s :=
begin
  rw language.mem_star at hy,
  rcases hy with ⟨ S, rfl, hS ⟩,
  induction S with a S ih,
  { refl },
  { have ha := hS a (list.mem_cons_self _ _),
    rw set.mem_singleton_iff at ha,
    rw [list.join, eval_from_of_append, ha, hx],
    apply ih,
    intros z hz,
    exact hS z (list.mem_cons_of_mem a hz) }
end

/- pump lemma的证明-/
/- 同样先限定σ是个finite type, x是α上的串, hx表明该串能被M接收-/
/- hlen表明x的长度要大于等于|σ|(也就是pump lemma里说的那个`N`)-/
/- 然后用∃对串进行拆分-/
lemma pumping_lemma [fintype σ] {x : list α} (hx : x ∈ M.accepts)
  (hlen : fintype.card σ ≤ list.length x) :
  ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ fintype.card σ ∧ b ≠ [] ∧
  {a} * language.star {b} * {c} ≤ M.accepts :=
begin
/- 首先利用上面的辅助定理`eval_from_split`进行拆分找到abc并获取相应的结论-/
  obtain ⟨_, a, b, c, hx, hlen, hnil, rfl, hb, hc⟩ := M.eval_from_split hlen rfl,
  use [a, b, c, hx, hlen, hnil],
  intros y hy,
  /-拆分hy-/
  rw language.mem_mul at hy,
  rcases hy with ⟨ ab, c', hab, hc', rfl ⟩,
  rw language.mem_mul at hab,
  /-再拆hab-/
  rcases hab with ⟨ a', b', ha', hb', rfl ⟩,
  rw set.mem_singleton_iff at ha' hc',
  substs ha' hc',
  have h := M.eval_from_of_pow hb hb',
  rwa [mem_accepts, eval_from_of_append, eval_from_of_append, h, hc]
end

end DFA
