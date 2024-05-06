module core.date.base where

open import core.base
open import core.natural
open import core.boolean.base
open import core.identity


data Month : Type where
    January   : Month
    February  : Month
    March     : Month
    April     : Month
    May       : Month
    June      : Month
    July      : Month
    August    : Month
    September : Month
    October   : Month
    November  : Month
    December  : Month

Year : Type
Year = ℕ

-- TODO: End-of-centry years must be divisible by 400
isLeapYear : Year → 𝔹
isLeapYear year with year % 4
... | Z     = true
... | suc b = false

daysOf : Year → Month → ℕ
daysOf year January = 31 
daysOf year February = if (isLeapYear year) then 29 else 28
daysOf year March = 31
daysOf year April = 30
daysOf year May = 31
daysOf year June = 30
daysOf year July = 31
daysOf year August = 31
daysOf year September = 30
daysOf year October = 31
daysOf year November = 30
daysOf year December = 31

Day : Year → Month → Type 
Day year month = Σ ℕ λ d → (1 ≤ d) × (d ≤ (daysOf year month))

test : Day 2024 February
fst test = 29 
_×_.fst (snd test) = 28 , ≡-refl
_×_.snd (snd test) = Z , ≡-refl