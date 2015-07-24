# Programs Accompanying the Thesis

The programs correspond to chapters 6, 7, 8 of part II.  They
are directly extracted from the thesis source file and listed
in the same order as they are in the thesis. They were
compiled with GHC version 7.8.3.

Page numbers in comments refer to the location of the code in
a previous version of the thesis, so they might not
correspond exactly to the last version.

Section headings are given in comments, in the format of the
outshine minor mode of Emacs, which allows to navigate the
structure of file easily and fold/unfold sections of the
program, very useful given when the files are big. I give
some instructions at the end of this file to configure Emacs
properly.

 - `Circular_6_1and2` contains the programs of chapter 6 section 1 and 2;
 - `Circular_6_3` contains the programs of chapter 6 section 3;
 - `Circular_7_1` contains the programs of chapter 7 section 1;
 - `Circular_7_2to5` contains the programs of chapter 7 section 2 to 5.

The git repository `ag-a-la-carte` contains the implementation of the
attribute grammar library discussed in section 8.4.

 - `Desk` is the example discussed in 8.4.1;
 - `Repmin` is another example not discussed in the thesis but
   related to chapter 6 and 7.

# Note on the use of arrow operators

In the thesis we used a type variable `~>` to stand for some
`Arrow` so that `a ~> b` stands for an arrow from `a` to `b`.
Such operator variables used to be allowed in GHC but they no
longer are. Instead, we can define types as operators.  Thus
we can devise the following trick (borrowed from E. Kmett),
using two type operators: `-` and `~>` defined such that `a
-h~> b` == `h a b`, for an arrow `h`. Those operators are
defined in `Circular_6_1and2`.


# Outshine minor mode

To use the outshine minor mode insert the following in your
`.emacs` file.  First install the package `outshine`, for
instance using the following:

    (require 'package)
    (add-to-list 'package-archives
                 '("melpa" . "http://melpa.milkbox.net/packages/"))
    (package-initialize)
    (unless (package-installed-p 'outshine)
       (package-install 'outshine))

Then activate it and use the correct regexp for recognising
section headings, and load outline minor mode when entering
Haskell mode.

    (require 'outshine)
    ; recognise section headings in comments
    (add-hook 'haskell-mode-hook  (lambda ()
        (setq outline-regexp "-- [*]\\{1,8\\} ")
        (outshine-fontify-headlines "-- [*]\\{1,8\\} ")))
    (add-hook 'haskell-mode-hook 'outline-minor-mode)

Then the following keystrokes are active when the cursor is
on a heading comment:
| Keystroke  | Action |
|------------|--------|
|`<TAB>`     | folds/unfolds a section
|`<M-TAB>`   | cycle through the following states: <p><ul><li>SHOW ALL where the file is displayed as normal</li><li>OVERVIEW where only the main headings are shown</li><li>CONTENTS where all the headings are shown</li></ul></p>
|`<M-right>` | unfolds a section
|`<M-left>`  | folds a section
|`<M-up>`    | previous heading
|`<M-down>`  | next heading

Additionally, you may want to rebind `outline` minor mode
commands to navigate more easily. Those commands are valid
anywhere in the file, not just on heading lines.

    (defun outshine-extra-bindings ()
      (local-set-key (kbd "C-M-h") 'hide-body)
      (local-set-key (kbd "C-M-S-h") 'hide-sublevels)
      (local-set-key (kbd "C-M-a") 'show-all)
      (local-set-key (kbd "C-M-<left>") 'outline-up-heading)
      (local-set-key (kbd "C-M-<right>") 
                     (lambda () (interactive)
                       (outline-up-heading 1)
                       (outline-forward-same-level 1)))
      (local-set-key (kbd "C-M-<up>") 'outline-backward-same-level)
      (local-set-key (kbd "C-M-<down>") 'outline-forward-same-level))
    (add-hook 'outline-minor-mode-hook 'outshine-extra-bindings)
