# Practice — no solutions in here

**Exercises, in the order the demo goes, so working through them is rehearsal.**
Nothing below is worked out for you and nothing tells you which command to
reach for. Each task says what to do and how you will know you got it; if you
cannot tell whether you got it, that is part of the task.

**Two rules for yourself.** Predict before you run — write down the answer you
expect, then check it. And when something refuses, read the refusal to the end
before changing anything: most of these tasks are really about whether the
refusals are good enough to present.

Start each section in a fresh session unless it says otherwise.

```
cabal run thena          # the REPL
cabal run thena-tui      # the four-pane interface
./tc ‹files…›            # batch, exits non-zero at the first file refused
```

---

## 1. Finding your way around with nothing loaded

1. Open the REPL and get it to list everything you can type. Then find the two
   commands in that list whose names you cannot explain to a stranger, and work
   out what they do without reading the manual.

2. Ask the system for the type of something in the prelude, then for its value.
   **You have got it when the two answers are different in kind** — one a
   statement, one a term — and you can say which command gave which.

3. Ask for the elimination rule of a prelude datatype. **You have got it when
   you can point at the part of what is printed that is the motive**, and say
   why it is a function and not a type.

4. Find a command that answers "what could I use here, given that I want
   something of this type". Use it on a type from the prelude. **You have got
   it when the answer is a list of names and you can see why each is in it.**

---

## 2. A language of your own

Work in a scratch file; do not edit the shipped ones.

5. Declare a language with two productions, load it, and write a term of it in
   its own notation. **You have got it when the term is accepted at the type
   your signature claims.**

6. Prove that a term written in the notation and the same term written as a
   constructor application are equal. **You have got it when the proof needs no
   argument you had to think about** — if you are reaching for a transport, the
   point of the exercise has been missed.

7. Make the parser refuse something. Then find a string it refuses for a
   *different* reason than the first one. **You have got it when the two
   messages differ in what they name**, not just in position.

8. Write a grammar in which some string parses two ways, and get the system to
   say so. **You have got it when the message shows you both parses.** Then
   change the grammar so that it does not, and say in one sentence what you
   changed about it — not about the string.

9. Start a parse at one named production rather than at the language's top, and
   find a string the whole language accepts and that production refuses.

10. Declare a language with a binder. Without writing a single line of
    substitution, find an input where substituting renames a binder, and prove
    what it renames it to. **You have got it when `refl` closes it** — which
    tells you something about where the work happened.

11. Ask that language for the free variables of a term with both a bound and a
    free occurrence of the same name. Predict the answer first.

---

## 3. Judgments

12. Load `Demo02Judgments.thena`. Get the system to print one of its judgments
    the way a paper prints it, and then the same judgment the way a type
    theorist would. **You have got it when you can match each rule in the first
    printing to exactly one constructor in the second.**

13. Pick a rule and work out, from the printed constructor alone, how many
    arguments it takes and in what order — **before** you try to apply it.
    Then build a derivation with it and see whether you were right. If you were
    not, find the sentence in the judgment block that decides the order.

14. Write a typing derivation for a term of your own choosing, three formers
    deep. **You have got it when the file loads with no trusted claims.**

15. Write a derivation that is wrong. Decide in advance which rule will be
    blamed, and whether the complaint will be about a type or about a term.

16. State a one-step reduction and prove it **without computing the
    right-hand side yourself** — let the kernel do it. Then state one whose
    right-hand side you got wrong on purpose, and read what it says.

17. Declare a judgment that is built on another judgment — a relation whose
    premises mention a relation you already have. **You have got it when it
    needs nothing new from the language.**

---

## 4. Proving by hand

18. Start a proof of something true and trivial and close it. **You have got it
    when the system prints the statement back at you with its mark.** Count the
    lines you needed; there is a shorter way than the one in the manual's first
    example, and finding it is the exercise.

19. Take a proof to the point where the **kernel** refuses it, rather than the
    elaborator. **You have got it when you can say which of the two refused**,
    from the words alone. Then find out what happened to the proof.

20. Get a proof into a state where `:where` tells you four things and you can
    say, for each, where it came from.

21. Split on a derivation. **Before you split, write down how many holes you
    expect and what will be in scope in each.** Then check. If a case
    disappeared, say which equation killed it.

22. Do that proof again, filling the cases in the opposite order. **You have got
    it when the result is the same term** — and you can say why the order was
    free.

23. Find a theorem statement for which the split's binders get printed with
    names you cannot type back into the prompt. **You have got it when you can
    say what it is about the statement that causes it**, and you can fix it by
    changing only the statement.

24. Add a hypothesis to a proof mid-way, use it, and then look at what the
    finished term did with it.

25. Undo. Find out exactly what `:undo` rewinds and what it leaves behind —
    there is at least one thing it leaves. **You have got it when you can
    demonstrate the leftover in three lines.**

26. Suspend a proof, prove something else, and come back to the first one.

27. Reduce a term in place inside a development, and then say whether the
    change was committed or only displayed.

---

## 5. The engine — this is the part the room will ask about

28. At an open hole, ask which rules apply. **You have got it when the answer is
    more than one** and you can say what would happen if the order of the rule
    base changed.

29. Choose a rule deliberately instead of letting the engine choose, and get it
    to fire.

30. Single-step the machine through an elaboration you understand. **You have
    got it when you can stop it at the instruction you predicted.**

31. Find a choice point and take a branch the engine did not take first. **You
    have got it when you end with a different term for the same goal.**

32. Open the shipped rule base and find the clause of `elaborate` that handled a
    construct you used in §2. **You have got it when you can read the clause
    aloud as a sentence about surface syntax.**

33. Write a rule of your own in a scratch rule base, put it on the stack, and
    get it to fire during an elaboration. **You have got it when removing your
    base changes the result.**

34. Answer this one in words, for the room: *what is the same object in
    "elaborating a definition" and "searching for a proof"?* Then find the place
    in the system where that sameness would be visible to a sceptic, and be
    ready to show it.

---

## 6. Saying "take my word for it"

35. Assert something false and find out which gate stops you, and at what
    moment relative to the kernel's own check.

36. Make a claim that is **pending** rather than impossible, build a theorem on
    top of it, and get the system to tell you what the theorem rests on.
    **You have got it when the report names the claim in the judgment's own
    notation.**

37. Discharge that claim and get the report to go clean. **You have got it when
    the trusted term is gone from what the system prints** — not merely allowed.

38. Find the setting under which the system will accept a provably false claim,
    put it back, and say in one sentence why only one of the three settings is a
    guarantee.

---

## 7. Modules

39. Make two modules, one importing the other, and have the importer take only
    some of what is exported. Then use a name you did not take.

40. Have a module withhold something, and find out at which point that is
    noticed.

41. Make two modules that each declare a language of the same name and load both.
    **You have got it when you can say what the refusal is really about.**

42. Type an `import` at the prompt rather than in a file, and then say what is
    different about how long it lasts.

43. Write a script of command lines by hand from a proof you have just done, and
    replay it. **You have got it when the replay ends where you ended.** Then
    say what a script's acts do that a module's do not.

---

## 8. The four-pane interface

44. Open the TUI and do task 21 again in it. **You have got it when you can say
    which pane told you something the REPL did not.**

45. Get the completion dropdown to offer you a term of an object language —
    inside a literal, not at the start of a line. **You have got it when the
    offers are the grammar's productions and not a word list.**

46. Watch the machine pane while an elaboration runs. Find a moment where it
    shows you something you would have had to ask for at the REPL.

47. Change the theme. Decide which one survives a projector, in a bright room,
    from the back.

---

## 9. Rehearsal

48. Do the whole of §2 from an empty file, out loud, in under eight minutes,
    without looking anything up.

49. Do §4 tasks 18, 21 and 22 out loud in under ten minutes.

50. Write down the three questions you would least like to be asked, and find
    where in the system each is answered. If one of them has no answer in the
    system, write that down too — it is a better thing to say than a guess.
