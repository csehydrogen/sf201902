# Software Foundations, SNU 4190.574, 2019 Fall

- Instructor: Prof. [Chung-Kil Hur](http://sf.snu.ac.kr/gil.hur)
    + Email address: gil.hur@sf.snu.ac.kr
    + Office: 302-426
- TA: [Juneyoung Lee](http://sf.snu.ac.kr/juneyoung.lee)
    + Email address: juneyoung.lee@sf.snu.ac.kr
    + Office: 302-312-2
- Class material: http://www.cis.upenn.edu/~bcpierce/sf/current/index.html
- Please use email to ask questions (Don't use GitHub Issues)

### Grading

- Exams: 40% (mid-term 20% and final 30%)
- Assignments: 45%
- Attendance: 5%

### Announcement

- Oct. 12: Assignment 2 is uploaded.
- Oct. 8: Midterm will be held on Oct. 26th Sat, 7 - 11 pm at 302동 소프트웨어실습실 (https://cse.snu.ac.kr/facility/소프트웨어-실험실 ).
- Sep. 28: Assignment 1 is uploaded.

### Assignments

- Visit http://147.46.242.54:8000 and log-in with your id (e.g. 2016-12345). Your initial password is equivalent to your id.

| Due        	| Description                   	 	 	 	 	 	 	 	 	 	 	 	 	 	|
|------------	|-----------------------------------------------------------------------------------
| Oct.6 23:59  	| Assignment 1                   	 	 	 	 	 	 	 	 	 	 	 	 	 	|
| Oct.20 23:59 	| Assignment 2                   	 	 	 	 	 	 	 	 	 	 	 	 	 	|


### Coq

- Install Coq [8.9.1](https://coq.inria.fr).
    + Using an installer (Windows, MacOS)
        * Download [Binaries](https://coq.inria.fr/download) and install it.

    + Using OPAM (Linux / MacOS)
        * OPAM is OCaml package manager, and you can use it to install Coq in Linux.
        * See [https://coq.inria.fr/opam/www/using.html](https://coq.inria.fr/opam/www/using.html).

    + Using brew (MacOS)
        * Run `brew install coq`, which will automatically install coq-8.9.1
        * Note this wouldn't install CoqIDE.

- Install IDE for Coq.
    + CoqIDE: installed by default.
    + Emacs: [Company-Coq](https://github.com/cpitclaudel/company-coq). Follow the setup instructions.
        * If it shows `Searching for program No such file or directory coqtop` error, please add `(custom-set-variables '(coq-prog-name "PATH/TO/coqtop"))` to `.emacs` file.
        * In case of MacOS, coqtop is at `/Applications/CoqIDE_8.9.1.app/Contents/Resources/bin/`.

