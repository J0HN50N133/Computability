import data.list.join
import data.set.lattice

/- # language -/
/- 这个文件定义了对字母表上的正则语言的定义和操作。注意: 字符串是作为字母表上的列表实现的。-/
open list set

universes v
variables {α β γ : Type*}
/- 一个语言是一个字母表`α`上的串的集合-/
/- derive utilities -/
/- derive complete_boolean_algebra则是因为正则语言可以交并补 -/
/- A Boolean algebra is a bounded distributive lattice with a complement operator `c`
 - such that `x ⊓ c(x) = ⊥` and `x ⊔ x = ⊤`. For convenience, it must also provice a set
 - difference operation '\' statisfying `x \ y = x ⊓ c(y)`
 - [https://en.wikipedia.org/wiki/Complete_Boolean_algebra]
 - [https://zh.wikipedia.org/wiki/%E5%B8%83%E5%B0%94%E4%BB%A3%E6%95%B0]
 -/
@[derive [has_mem (list α), has_singleton (list α), has_insert (list α), complete_boolean_algebra]]
def language (α) := set (list α)

namespace language
variables {l m: language α} {a b x: list α}
local attribute [reducible] language

/- 空语言没有元素 -/
instance : has_zero (language α) := ⟨(∅ : set _)⟩
/- `1: language α` 接受空串的语言 -/
instance : has_one (language α) := ⟨{[]}⟩
instance : inhabited (language α) := ⟨0⟩
/- 可以并 -/
instance : has_add (language α) := ⟨(∪)⟩
/- 可以笛卡尔积 -/
instance : has_mul (language α) := ⟨image2 (++)⟩

lemma zero_def : (0: language α) = (∅ : set _) := rfl
lemma one_def : (1: language α) = {[]} := rfl

lemma add_def (l m : language α) : l + m = l ∪ m := rfl
lemma mul_def (l m : language α) : l * m = image2 (++) l m := rfl

/- 定义克林闭包运算,这里没有采用结构归纳定义,使用了字符串拼接来定义 -/
/- 这个定义的意思是：语言`l`的克林闭包里的每一个元素，都可以由`l`里的-/
/- 任意多个串拼接而成-/
/- 例如`l={0,1}`, `0101 ∈ l*`, `0101=[0,1,0,1].join`-/
def star (l : language α) : language α :=
{x| ∃ S: list (list α), x = S.join ∧ ∀ y∈ S, y ∈ l}
lemma star_def (l: language α) :
  l.star = {x| ∃ S: list (list α), x = S.join ∧ ∀ y∈ S, y ∈ l} := rfl

@[simp] lemma not_mem_zero (x:list α) : x∉ (0:language α) := id
@[simp] lemma mem_one (x:list α) : x∈ (1:language α) ↔ x = [] := by refl
lemma nil_mem_one : [] ∈ (1 : language α) := set.mem_singleton _
@[simp] lemma mem_add (l m: language α) (x : list α) : x∈ l+m ↔ x ∈ l ∨ x ∈ m := iff.rfl
lemma mem_mul : x ∈ l * m ↔ ∃ a b, a ∈ l ∧ b ∈ m ∧ a ++ b = x := mem_image2
lemma append_mem_mul : a ∈ l → b ∈ m → a++b ∈ l*m := mem_image2_of_mem
lemma mem_star : x ∈ l.star ↔ ∃ S : list (list α), x = S.join ∧ ∀ y ∈ S, y∈ l := iff.rfl
lemma join_mem_star {S: list (list α)} (h: ∀ y∈ S, y∈ l) : S.join ∈ l.star :=
⟨S, rfl, h⟩
lemma nil_mem_star (l : language α): [] ∈ l.star := ⟨[], rfl, λ _, false.elim⟩

/- 正则语言的半环结构 -/
instance : semiring (language α) :=
{ add := (+),
  add_assoc := union_assoc,
  zero := 0,
  zero_add := empty_union,
  add_zero := union_empty,
  add_comm := union_comm,
  mul := (*),
  mul_assoc := λ _ _ _, image2_assoc append_assoc,
  zero_mul := λ _, image2_empty_left,
  mul_zero := λ _, image2_empty_right,
  one := 1,
  one_mul := λ l, by simp [mul_def, one_def],
  mul_one := λ l, by simp [mul_def, one_def],
  left_distrib := λ _ _ _, image2_union_right,
  right_distrib := λ _ _ _, image2_union_left}

@[simp] lemma add_self (l : language α) : l + l = l := sup_idem

/- Ring homomorphism -/
def map (f : α → β) : language α →+* language β :=
{ to_fun := image (list.map f),
  map_zero' := image_empty _,
  map_one' := image_singleton,
  map_add' := image_union _,
  map_mul' := λ _ _, image_image2_distrib $ map_append _}
end language
