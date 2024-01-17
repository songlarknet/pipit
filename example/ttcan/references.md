# References

## Environment and assumptions
Assuming a CAN bus clock of 1Mbps, we get around 10,000 messages per second. For a CPU of >100MHz, we have a budget of >10K instructions per message.


## CAN implementation and driver details

TTCAN standard:
* http://rafavi.com/images/CAN_pdf/ISO11898/ISO_11898-4-2004.pdf

M_TTCAN hardware / FPGA module
* https://www.bosch-semiconductors.com/media/ip_modules/pdf_2/m_can/mttcan_users_manual_v330.pdf

MCP2515 SPI-controlled CAN controller:
* datasheet: https://ww1.microchip.com/downloads/en/DeviceDoc/MCP2515-Stand-Alone-CAN-Controller-with-SPI-20001801J.pdf

CAN4LINUX:
* https://gitlab.com/hjoertel/can4linux/-/blob/master/can4linux/can4linux.h?ref_type=heads
* https://gitlab.com/hjoertel/can4linux/-/blob/master/can4linux/defs.h?ref_type=heads
* https://gitlab.com/hjoertel/can4linux/-/blob/master/can4linux/read.c?ref_type=heads
* https://gitlab.com/hjoertel/can4linux/-/blob/master/can4linux/write.c?ref_type=heads

SocketCAN: Linux drivers for CAN as a network device
* documentation: https://www.kernel.org/doc/html/latest/networking/can.html
* unclear if this interface is suitable for time-triggered and real-time

Can2040: software implementation of CAN bus for rp2040 microcontroller
* implementation: https://github.com/KevinOConnor/can2040
* supports real-time, assuming low IRQ latency from other running software
* strongly encourages running on a dedicated core

## Time-triggered networks

Networking and communications in autonomous driving: a survey, 2018
* Jiadai Wang, Jiajia Liu, Nei Kato.
* DOI 10.1109/COMST.2018.2888904
* https://ieeexplore.ieee.org/stamp/stamp.jsp?arnumber=8584062&casa_token=nmI7VWpVp5kAAAAA:a_ORuGV0BHKj7rLat1r1MJ8OdTLaRSHYp-iU7CDMnlIDpVtmesZWs1A1zyOdZPAuzjBmUSXh&tag=1
* README

A time-predictable open-source TTEthernet end-system, 2020
* Kyriakakis, Lund, Pezzarossa, Sparsø, Schoeberl
* https://doi.org/10.1016/j.sysarc.2020.101744
* https://www.sciencedirect.com/science/article/pii/S1383762120300382
* implementation: https://github.com/t-crest/patmos
* implementation of time-triggered ethernet on "Patmos" processor
* PI controller to control for clock errors

Towards modularized verification of distributed time-triggered systems, 2006
* Botaschanjan, Gruler, Harhurin, Kof, Spichkova, Trachtenherz
* https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=45e97c5645704b408609e51aad95d3b2f50b19c5

Modeling and verification of CAN bus with application layer using UPPAAL, 2014
* Pan, Guo, Zhu
* https://core.ac.uk/download/pdf/82439813.pdf
* models CAN bus itself to show deadlock freedom and some other properties
* models bus-off and failure counters

A finite state analysis of time-triggered CAN (TTCAN) protocol using Spin, 2007
* Indranil Saha and Suman Roy
* https://sci-hub.se/https://ieeexplore.ieee.org/document/4127346
* see Leen and Heffernen [11] for UPPAAL specification of TTCAN
* list of desirable properties: progression-of-time; starvation freedom; data consistency; bus off; bus access method; automatic retransmission; remote data request; error signaling; fault tolerance
* short, lacks detail

Modeling and verification of a time-triggered networking protocol, 2006
* Leen, Heffernan
* https://core.ac.uk/download/pdf/59347169.pdf
* UPPAAL model
* some detail about master ref and matrix
* strong assumptions about underlying bus, eg no transmission errors

Model checking a TTCAN implementation, 2011
* Daniel Keating, Allan McInnes, Michael Hayes
* https://sci-hub.se/https://ieeexplore.ieee.org/document/5770628
* SPIN model
* uses abstract details of CAN
* separate models for basic operation and master election, as well as for joining redundant buses
* still confused about detail of master election

Formal modeling and verifying the TTCAN protocol from a probabilistic perspective, 2018
* Xin Li, Jian Guo, Yongxin Zhao, Xiaoran Zhu
* https://sci-hub.se/https://www.worldscientific.com/doi/epdf/10.1142/S0218126619501779

A review on formal verification of basic algorithms in time triggered architecture, 2018
* Sheena N., Shelbi Joseph, Suresh Kumar N.
* https://ieeexplore.ieee.org/stamp/stamp.jsp?arnumber=8574228&casa_token=_ksZ8hYq9KAAAAAA:KV0wmYJ-5f8lt8-KCpi_YtjmnWwQ64TTVhZ1isxxvhXNJsf4FehTtmtX4keRpvf_GtqY7u6S&tag=1
* brief survey of formally verified TTA algorithms

Model checking of in-vehicle networking systems with CAN and FlexRay, 2019
* Xiaoyun Guo, Toshiaki Aoki, Hsin-Hung Lin

Model checking of TTCAN protocol using UPPAAL, 2018
* Liu Shuxin and Noriaki Yoshiura
* https://sci-hub.se/https://link.springer.com/chapter/10.1007/978-3-319-95171-3_43
* key idea: separate out master arbitration phase and message transmission phase; verify separately, with message transmission phase assuming master arbitration has successfully completed
* describes core algorithms of TTCAN with examples, but not sure if there's enough detail to reproduce


## FlexRay
FlexRay is the successor to CAN.

