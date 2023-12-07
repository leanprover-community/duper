__Debugging__
* To debug unification procedure, use
  ```
  set_option trace.duper.dUnif.debug true
  ```
* To enable advanced debugging functionality, use
  ```
  set_option dUnifDbgOn true
  ```
* The ```contains <k>``` option of ```dapply``` and ```drefl``` is useless when ```dUnifDbgOn``` is ```false```, because we do not push parent clause and can't check ```contains``` when ```dUnifDbgOn``` is ```false```.