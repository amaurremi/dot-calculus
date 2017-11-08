# Alternative DOT Proof

## Old Possible Types Lemma

    Γ ~ s   s(x) = v   Γ ⊢ x: T
    ---------------------------
            T ∈ PT(Γ,x,v)

## New Possible Types Lemma

    Γ inert   Γ(x) = T   Γ ⊢ x: U
    -----------------------------
            U ∈ PT(Γ,x,T)

## Inert Types

    inert ∀(x: S)T

        record T
    ----------------
      inert μ(x: T)

## Inert Environments

    inert {}

        x # Γ
        inert Γ
        inert T
    ---------------
    inert (Γ, x: T)
