function convert() {
   var currencyFrom = document.getElementById("currency_from").value;
   var currencyTo = document.getElementById("currency_to").value;
   var amount = document.getElementById("amount").value;
   var resultTag = document.getElementById("result");
   var url = "http://mehdi.bouaziz.org/jsx/services/curr.php?i="+currencyFrom+"&o=" + currencyTo+"&a="+amount;
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
