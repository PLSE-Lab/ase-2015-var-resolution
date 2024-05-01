Introduction
------------

This repository contains the files supporting our recent ASE submission, available
[here](https://cs.appstate.edu/hillsma/publication/ase-2015/). Note that we are currently working on improvements to the algorithms, so there are some slight differences between the numbers in the paper and those that are currently generated if you run the patterns on the corpus. Also, there was a renaming bug when the patterns were renamed to match the names in the paper (originally they were just given numbers, like pattern 01, pattern 14, etc). This does not effect the numbers reported in the paper.

Running Our Software
--------------------

To run this software, you will need to download and configure the PHP AiR system. This is [available on GitHub](https://github.com/cwi-swat/php-analysis/) and includes installation instructions.

After installing, you should add the PHPAnalysis project as a plugin dependency. More information will be following soon.

The corpus used for this analysis is included as a file in this repository, under Downloads.

UPDATE: We are in the process of moving prior work over to a format that works well with VSCode
instead of requiring Eclipse. The code here works regardless of the environment, but we still
need to add the proper library info for it to find PHP AiR.
