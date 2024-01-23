# Artifact Submission Template

Title of the submitted paper: Pipit on the Post: Proving Pre- and Post-conditions of Reactive Systems
ECOOP submission number for the paper: 22

## Metadata to provide during artifact submission in HotCRP

## Quick-start guide (Kick-the-tires phase)

Load the docker image:
```
docker load -i pipit.tar
```
(Note that Docker commands might require `sudo` on Linux. We omit the `sudo` here.)

Open a shell with the docker image:
```
docker run -it pipit
```

From within docker, generate the code for the simple example (3s):
```docker-shell
make extract-simple
cat build/extract/simple/Simple_Extract.c
```

The above example will generate some warnings as it uses arbitrary-precision integer arithmetic; the TTCAN example uses machine-checked arithmetic.

Run the Kind2 evaluation on very small arrays (15s):
```docker-shell
example/ttcan/lus/run-eval.sh 2
```

The above will print part of the LaTeX table corresponding to figure 11. The format is described below under heading S6.2 Verification.

## Overview: What does the artifact comprise?

* Code (F*): Pipit: the implementation of Pipit itself is in src/*.fst. See src/readme.md for high-level descriptions of module structure.
* Proofs (F*): all theorems mentioned in the paper are mechanised in F*. See src/readme.md for locations of each theorem.
* Code (F*,Pipit): TTCAN (S2,S6): the implementation of the TTCAN example is in example/ttcan/*.fst.
* Proof (F*,Pipit): TTCAN (S2,S6): the TTCAN proof is in example/ttcan/Network.TTCan.TriggerTimely.fst.
* Experiment (Lustre,Bash): comparison-to-Kind2 (Figure 11): example/ttcan/lus/trigger_*.lus, example/ttcan/lus/run-eval.sh
* Experiment (C,CSV): extracted TTCAN runtime (S6.1): example/ttcan/bench/runtimes.csv

## For authors claiming an available badge

Apache 2.0 License

## For authors claiming a functional or reusable badge

### S6.1 Runtime

Section 6.1 states that the TTCAN example takes 114µs on a Raspberry Pi Pico (RP2040).
Reproducing this experiment requires dedicated hardware and manual steps.
The motivation behind this claim is also somewhat informal, as we aren't making any direct speed comparisons: we just wanted to provide evidence that the generated code is fast enough to be useful.
If it turns out to be too difficult for others to reproduce this claim, we are happy to remove the claim or perform the benchmark on a more-accessible target.

While packaging this experiment into a Docker container, we encountered two discrepancies from the original experiment: first, the binaries produced by the Docker image are somewhat slower (+~30µs); secondly, the USB-UART interface introduces significant overhead compared to the raw UART interface (+>50µs). We are still investigating the version differences that lead to the first discrepancy. For the second, we hypothesise that the USB-UART driver requires some processing overhead, while the raw UART interface is likely handled completely by DMA.

Using the raw UART interface would reduce this overhead, but it requires more hardware (a debugger or second Raspberry Pi Pico), and the configuration is more complex.
To simplify reproduction, we have modified the benchmark to record all of the times before initialising the USB-UART; then, when the UART is connected, it prints the results.

The amended benchmark resolves the second discrepancy, but not the first discrepancy of using a different toolchain. The results are still a little slower than the paper version. If the paper is accepted, we can update the paper to use the slower times; this regression does not detract significantly from the claims made in the paper.

The pre-built Pico binaries are in `example/ttcan/bench/app_can_time.*`. **Optionally,** to rebuild them run the following:
```
# Load the Pico SDK Docker image (NB: this is a different image from the one used above)
docker build -t pipit-pico -f example/ttcan/bench/Dockerfile .
docker run -it -v ${PWD}/example/ttcan/bench:/bench-out pipit-pico cp app_can_time.uf2 app_can_time.elf /bench-out
```

Now, depress the `BOOTSEL` button on your Raspberry Pi Pico, then connect it via USB with the button still pressed. Release the button after plugging it in. The `BOOTSEL` button activates the internal USB bootloader, which acts as a USB storage device. To program the Pico, copy the `UF2` binary onto the storage device. On MacOS, the command for this is:
```
cp example/ttcan/bench/app_can_time.uf2 /Volumes/RPI-RP2
```

After programming the Pico, we connect to the USB-UART serial terminal. The exact path of the serial terminal will be different. On MacOS, this shows as `/dev/cu.usbmodem<NUM>`. On Linux, it may show as `/dev/ttyACM<NUM>`.
To test it, you can get the first few lines with `head`:
```
head -n 3 /dev/cu.usbmodem11301
90
88
91
```

Each line is an iteration time in µs. If the lines come out jumbled, then it may be necessary to specify the baud rate; use a console reader such as screen (`screen /dev/cu.usbmodem11301 115200`).

If the above `head` command worked, we can then take 5,000 samples. This should take around five seconds:
```
head -n 5000 /dev/cu.usbmodem11301 > out.csv
```

I then opened the CSV in Numbers / Excel to get the minimum, maximum, average, and standard deviation.
In this execution, I observed measurements in the range 86-140µs; we will update the paper to match these new results.

### S6.2 Verification

To generate the data for Figure 11 S6.2, experimental comparison to Kind2, run:
```
docker run -it pipit example/ttcan/lus/run-eval.sh 6
```
This script will take approximately 15 minutes to run.
The script generates a LaTeX table which is pasted into the paper.
The format is unfortunately not particularly human-readable.
The table has three comparisons: Kind2 with simplified enable-set, Kind2 with full enable-set, and Pipit.
The rows are: array-size; simple-enable wall-clock; simple-enable user-time; full-enable wall-clock; full-enable user-time; Pipit wall-clock; Pipit user-time.
A row looks like this:
```
1 & 1.48s&1.24s
 & 1.62s&2.53s
 & 8.21s&7.89s \\
```
This says that for arrays of size 1, Kind2 simple took 1.48s wall-clock, Kind2 full took 1.62 wall-clock, and Pipit took 8s.
(The Pipit proof is once-and-for-all so we don't re-run it for each row, but just include it for comparison.)

The paper also claims that for sizes of 64, the verification timed out after three hours. To reproduce this, run the above script with 7 rows instead of 6:
```
docker run -it pipit example/ttcan/lus/run-eval.sh 7
```
This script will take several hours; we were unable to include the finished times in the submitted paper due to time constraints.


## For authors claiming a reusable badge

Our implementation is open-source. The software can be recompiled by running `make -j8` in the `pipit` docker image:
```
docker run -it pipit
make -j8
```

Instructions for building outside of Docker are detailed in readme.md.

Pipit is an embedded programming language; the most likely reuse of Pipit involves users writing programs, and using Pipit to verify them and generate executable code. Pipit would be suitable for controllers in critical domains such as automotive controllers and industrial systems.
