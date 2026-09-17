import Proof

open Erdos635

#print axioms Erdos635.maxAdm_eq
#print axioms Erdos635.isGreatest_adm_card
#print axioms Erdos635.card_le_of_adm
#print axioms Erdos635.adm_odds
#print axioms Erdos635.card_odds

example : ∀ N : ℕ, maxAdm N = (N + 1) / 2 := Erdos635.maxAdm_eq
example : ∀ N : ℕ, IsGreatest {m : ℕ | ∃ A : Finset ℕ, Adm N A ∧ A.card = m} ((N + 1) / 2) :=
  Erdos635.isGreatest_adm_card
example : ∀ (N : ℕ) (A : Finset ℕ), Adm N A → A.card ≤ (N + 1) / 2 := Erdos635.card_le_of_adm
example : ∀ N : ℕ, Adm N ((Finset.Icc 1 N).filter (fun n => ¬ 2 ∣ n)) := Erdos635.adm_odds
example : ∀ N : ℕ, ((Finset.Icc 1 N).filter (fun n => ¬ 2 ∣ n)).card = (N + 1) / 2 :=
  Erdos635.card_odds

#print Erdos635.Adm
#print Erdos635.maxAdm
