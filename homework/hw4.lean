import Mathlib
/-!
# Инструкция по выполнению ДЗ №4.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.

Могут оказаться полезными:
* Индуктивные типы, ключевое слово `match`.
* Тактика `induction`.

Не стесняйтесь задавать вопросы в чате!
-/
open Function

/-- Задача 1. `BinTree` это тип бинарных деревьев, на листьях которого написаны натуральные числа.
Ваша задача -- определить функцию `BinTree.sum` которая вычисляет сумму этих чисел. После этого проверьте
что "тесты" ниже могут быть доказаны с помощью `by rfl`.
-/
inductive BinTree
| leaf (val : ℕ)
| node (left : BinTree) (right : BinTree)

def BinTree.sum (tree : BinTree) : ℕ := match tree with
| leaf (val : ℕ) => val
| node (left : BinTree) (right : BinTree) => (BinTree.sum left) + (BinTree.sum right)


-- Тесты
example (v : ℕ) : BinTree.sum (BinTree.leaf v) = v := by rfl --rfl
example : BinTree.sum (BinTree.node (.leaf 3) (.node (.node (.leaf 2) (.leaf 1)) (.leaf 4))) = 10 := by rfl --rfl

/-- Задача 2. Определите предикат `BinTree.AllEven` означающий что все написанные на листьях числа четны.
Проверьте что "тесты" ниже могут быть доказаны через `by reduce; norm_num`. Затем докажите теорему ниже.

Примечание: чтобы это сработало выражайте факт "`n` - четное" как `n % 2 = 0`.

Примечание №2: `reduce` это тактика которая приводит все термы в цели к нормальной форме. В частности она
раскрывает определения и определяет по какой ветви `match` пойти.
-/
def BinTree.AllEven (tree : BinTree) : Prop := match tree with
| leaf (val : ℕ) => val % 2 = 0
| node (left : BinTree) (right : BinTree) => (BinTree.AllEven left) ∧ (BinTree.AllEven right)

-- Тесты
example : BinTree.AllEven (.leaf 3) = False := by reduce ; norm_num --reduce; norm_num
example : BinTree.AllEven (.leaf 2048) = True := by reduce ; norm_num --reduce; norm_num
example : BinTree.AllEven (.node (.leaf 3) (.node (.node (.leaf 2) (.leaf 1)) (.leaf 4))) = False := by reduce ; norm_num --reduce; norm_num
example : BinTree.AllEven (.node (.leaf 8) (.node (.node (.leaf 8) (.leaf 0)) (.leaf 4))) = True := by reduce ; norm_num --reduce; norm_num

-- Теорема
example (tree : BinTree) (h_even : tree.AllEven) : tree.sum % 2 = 0 := by
  induction' tree with val left right ihl ihr
  · unfold BinTree.AllEven at h_even
    unfold BinTree.sum
    assumption
  · unfold BinTree.AllEven at h_even
    unfold BinTree.sum
    obtain ⟨ hlev, hrev ⟩ := h_even
    specialize ihl hlev
    specialize ihr hrev
    omega


/-- Задача 3: Существует счетная цепочка типов `Fₙ` такая что `Fₙ` можно инъективно и строго вложить
в `Fₙ₊₁`, и при этом `Fₙ₊₁ ≠ Fₙ`. -/
example : ∃ F : ℕ → Type, ∀ n, ∃ ι : F n → F (n + 1), Injective ι ∧ ι '' Set.univ ≠ Set.univ := by
  use (fun (_ : ℕ ) => ℕ)
  intro n
  use (fun (n : ℕ) => 2 * n)
  constructor
  · intro m k hmk
    simp at hmk
    assumption
  · intro heq
    have prop₀ : 1 ∈ Set.univ := by trivial
    rw [← heq] at prop₀
    obtain ⟨ N, hN ⟩ := prop₀
    obtain ⟨ hNℕ, hNev ⟩  := hN
    reduce at hNev
    apply Nat.not_even_one
    use N
    ring_nf
    rw [mul_comm N 2]
    apply Eq.symm
    assumption
