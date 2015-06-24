function convert() {
   var currencyFrom = document.getElementById("currency_from").value;
   var currencyTo = document.getElementById("currency_to").value;
   var amount = document.getElementById("amount").value;
   var resultTag = document.getElementById("result");
   var url;
   if (amount == 1)
       url = "http://mehdi.bouaziz.org/jsx/services/curr.php?i="+currencyFrom+"&o=" + currencyTo+"&a=1";
   else if (amount == 2)
       url = "http://mehdi.bouaziz.org/jsx/services/curr.php?i="+currencyFrom+"&o=" + currencyTo+"&a=2";
   else {
       resultTag.value = "I don't know";
       return false;
   }
   var rq = new XMLHttpRequest();
   rq.open('GET', url, false);
   try {
      rq.send();
      if (rq.status == 200)
	  resultTag.value = rq.responseText;
      else
	  resultTag.value = "ERROR";
   } catch (x) {
      alert("AJAX request failed");
   }
}
