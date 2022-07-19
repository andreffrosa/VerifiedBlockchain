### CVS's Lab Project

Project description: [Readme.pdf](Readme.pdf)

Run: `java Main [options]`

Options:
```
-p Number of transaction producers
-w Number of block workers
-q Transaction queue size
-d Discard failed transactions flag, else re-inserts in queue
-r Maximum number of retries per block
-s Maximum sleep between retries
-t Log sleep interval				
```
