function convert() {
   var currencyFrom = document.getElementById("currency_from").value;
   var currencyTo = document.getElementById("currency_to").value;
   var amount = document.getElementById("amount").value;
   var resultTag = document.getElementById("result");
   var url = "http://mehdi.bouaziz.org/jsx/services/curr.php?i="+currencyFrom+"&o=" + currencyTo;
   var rq = new XMLHttpRequest();
   rq.open('GET', url, false);
   try {
      rq.send();
      var rate;
      if (rq.status == 200) {
	  rate = rq.responseText;
	  resultTag.value = rate * amount;
      }
      else
	  resultTag.value = "ERROR";
   } catch (x) {
      alert("AJAX request failed");
   }
}
