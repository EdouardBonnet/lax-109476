import Lax109476Proofs.RamFrame

namespace Lax109476Proofs.RamArrayRelabel

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def expression (f : String → String) : Expr → Expr
  | .lit v => .lit v
  | .var x => .var x
  | .get a i => .get (f a) (expression f i)
  | .bin op e g => .bin op (expression f e) (expression f g)

def condition (f : String → String) : Cond → Cond
  | .eq e g => .eq (expression f e) (expression f g)
  | .lt e g => .lt (expression f e) (expression f g)

def command (f : String → String) : Com → Com
  | .skip => .skip
  | .assign x e => .assign x (expression f e)
  | .store a i e => .store (f a) (expression f i) (expression f e)
  | .seq c d => .seq (command f c) (command f d)
  | .ite b c d => .ite (condition f b) (command f c) (command f d)
  | .while b c => .while (condition f b) (command f c)
  | .read x => .read x
  | .write e => .write (expression f e)

def view (f : String → String) (σ : Env) : Env := {σ with arrs := fun a => σ.arrs (f a)}

@[simp] theorem expression_size (f : String → String) (e : Expr) :
    (expression f e).size = e.size := by
  induction e <;> simp_all [expression, Expr.size]

@[simp] theorem condition_size (f : String → String) (b : Cond) :
    (condition f b).size = b.size := by
  cases b <;> simp [condition, Cond.size]

@[simp] theorem expression_eval (f : String → String) (e : Expr) (B : ℕ) (σ : Env) :
    (expression f e).evalB B σ = e.evalB B (view f σ) := by
  induction e <;> simp_all [expression, Expr.evalB, view]

@[simp] theorem condition_eval (f : String → String) (b : Cond) (B : ℕ) (σ : Env) :
    (condition f b).evalB B σ = b.evalB B (view f σ) := by
  cases b <;> simp [condition, Cond.evalB]

@[simp] theorem view_setVar (f : String → String) (σ : Env) (x : String) (v : ℕ) :
    view f (σ.setVar x v) = (view f σ).setVar x v := rfl

@[simp] theorem view_setArr (f : String → String) (hf : Function.Injective f)
    (σ : Env) (a : String) (k v : ℕ) :
    view f (σ.setArr (f a) k v) = (view f σ).setArr a k v := by
  cases σ
  simp only [view, Env.setArr]
  congr 1
  funext x
  by_cases hx : x = a
  · subst x; simp
  · have hfx : f x ≠ f a := fun h => hx (hf h)
    simp [hx, hfx]

/-- Array relabeling permits finitely many fixed copies of the same proved
routine with distinct workspace dimensions in a single uniform program. -/
theorem run_relabel {B k : ℕ} {c : Com} {σ τ : Env} (f : String → String)
    (hf : Function.Injective f) (h : BigStepB B c σ τ k) :
    ∀ β, view f β = σ → ∃ γ, BigStepB B (command f c) β γ k ∧ view f γ = τ := by
  induction h with
  | skip => intro β hβ; exact ⟨β, .skip, hβ⟩
  | @assign σ x e v he =>
    intro β hβ
    refine ⟨β.setVar x v, ?_, by simp [hβ]⟩
    simpa only [command, expression_size] using
      (BigStepB.assign (B := B) (σ := β) (x := x) (e := expression f e) (by simpa only [expression_eval, hβ] using he))
  | @store σ a i e k v hi he hk =>
    intro β hβ
    have hlen : k < (β.arrs (f a)).length := by simpa only [← hβ, view] using hk
    refine ⟨β.setArr (f a) k v, ?_, by simp [hf, hβ]⟩
    simpa only [command, expression_size] using BigStepB.store (B := B) (σ := β) (a := f a) (i := expression f i) (e := expression f e)
      (by simpa only [expression_eval, hβ] using hi)
      (by simpa only [expression_eval, hβ] using he) hlen
  | seq hc hd ihc ihd =>
    intro β hβ
    obtain ⟨γ, hγ, heγ⟩ := ihc β hβ
    obtain ⟨δ, hδ, heδ⟩ := ihd γ heγ
    exact ⟨δ, hγ.seq hδ, heδ⟩
  | @ite_true b c d σ σ' k hb hc ih =>
    intro β hβ
    obtain ⟨γ, hγ, heγ⟩ := ih β hβ
    exact ⟨γ, by simpa only [command, condition_size] using
      BigStepB.ite_true (B := B) (σ := β) (b := condition f b) (d := command f d) (by simpa only [condition_eval, hβ] using hb) hγ, heγ⟩
  | @ite_false b c d σ σ' k hb hd ih =>
    intro β hβ
    obtain ⟨γ, hγ, heγ⟩ := ih β hβ
    exact ⟨γ, by simpa only [command, condition_size] using
      BigStepB.ite_false (B := B) (σ := β) (b := condition f b) (c := command f c) (by simpa only [condition_eval, hβ] using hb) hγ, heγ⟩
  | @while_true b c σ σ' σ'' k k' hb hc hw ihc ihw =>
    intro β hβ
    obtain ⟨γ, hγ, heγ⟩ := ihc β hβ
    obtain ⟨δ, hδ, heδ⟩ := ihw γ heγ
    exact ⟨δ, by simpa only [command, condition_size] using
      BigStepB.while_true (B := B) (σ := β) (b := condition f b) (by simpa only [condition_eval, hβ] using hb) hγ hδ, heδ⟩
  | @while_false b c σ hb =>
    intro β hβ
    exact ⟨β, by simpa only [command, condition_size] using
      BigStepB.while_false (B := B) (σ := β) (b := condition f b) (c := command f c) (by simpa only [condition_eval, hβ] using hb), hβ⟩
  | @read σ x v rest hi =>
    intro β hβ
    refine ⟨{β.setVar x v with inp := rest}, ?_, ?_⟩
    · exact BigStepB.read (by simpa only [← hβ, view] using hi)
    · change {view f (β.setVar x v) with inp := rest} = _
      simp only [view_setVar, hβ]
  | @write σ e v he =>
    intro β hβ
    refine ⟨{β with out := β.out ++ [v]}, ?_, ?_⟩
    · simpa only [command, expression_size] using BigStepB.write (B := B) (σ := β) (e := expression f e)
        (by simpa only [expression_eval, hβ] using he)
    · change {view f β with out := (view f β).out ++ [v]} = _
      rw [hβ]

theorem spec_relabel {B K : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com}
    (f : String → String) (hf : Function.Injective f) (h : Spec B P c Q K) :
    Spec B (fun σ => P (view f σ)) (command f c)
      (fun σ τ => Q (view f σ) (view f τ)) K := by
  intro β hβ
  obtain ⟨τ, ⟨k, hk, hr⟩, hτ⟩ := h (view f β) hβ
  obtain ⟨γ, hγ, heγ⟩ := run_relabel f hf hr β rfl
  exact ⟨γ, ⟨k, hk, hγ⟩, by change Q (view f β) (view f γ); rw [heγ]; exact hτ⟩

def prefixed (name : String) (c : Com) : Com := command (fun a => name ++ a) c

theorem prefix_injective (name : String) : Function.Injective (fun a => name ++ a) :=
  fun _ _ h => (String.append_right_inj name).mp h

theorem spec_prefixed {B K : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com}
    (name : String) (h : Spec B P c Q K) :
    Spec B (fun σ => P (view (fun a => name ++ a) σ)) (prefixed name c)
      (fun σ τ => Q (view (fun a => name ++ a) σ) (view (fun a => name ++ a) τ)) K :=
  spec_relabel _ (prefix_injective name) h

end Lax109476Proofs.RamArrayRelabel
