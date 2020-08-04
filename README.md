Stadeo
======

Stadeo is a set of tools primarily developed to facilitate analysis of
[Stantinko](https://www.welivesecurity.com/2017/07/20/stantinko-massive-adware-campaign-operating-covertly-since-2012/),
which is a botnet performing click fraud, ad injection, social network
fraud, password stealing attacks and
[cryptomining](https://www.welivesecurity.com/2019/11/26/stantinko-botnet-adds-cryptomining-criminal-activities/).

The scripts, written entirely in Python, deal with Stantinko's unique
control-flow-flattening (CFF) and string obfuscation techniques
described in our March 2020
[blogpost](https://www.welivesecurity.com/2020/03/19/stantinko-new-cryptominer-unique-obfuscation-techniques/).
Additionally, they can be utilized for other purposes: for example,
we’ve already extended our approach to support deobfuscating the CFF
featured in Emotet – a trojan that steals banking credentials and that
downloads additional payloads such as ransomware.

Our deobfuscation methods use
[IDA](https://www.hex-rays.com/products/ida/), which is a standard tool
in the industry, and [Miasm](https://github.com/cea-sec/miasm) – an open
source framework providing us with various data-flow analyses, a
symbolic execution engine, a dynamic symbolic execution engine and the
means to reassemble modified functions.
