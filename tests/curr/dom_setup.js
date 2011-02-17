x = (function() {

    function createCurrencyOption(code) {
       var option = document.createElement("option");
       option.value = code;
       var txt = document.createTextNode(code);
       option.appendChild(txt);
       return option;
    }

    var form=document.createElement("form");
    var currency_from_label=document.createElement("label");
    currency_from_label.appendChild(document.createTextNode("From "));
    form.appendChild(currency_from_label);
    var currency_from = document.createElement("select");
    currency_from.setAttribute("id", "currency_from");
    currency_from.appendChild(createCurrencyOption("USD"));
    currency_from.appendChild(createCurrencyOption("EUR"));
    currency_from.appendChild(createCurrencyOption("RUB"));
    form.appendChild(currency_from);
    var currency_to_label=document.createElement("label");
    currency_to_label.appendChild(document.createTextNode(" to "));
    form.appendChild(currency_to_label);
    var currency_to = document.createElement("select");
    currency_to.setAttribute("id", "currency_to");
    currency_to.appendChild(createCurrencyOption("USD"));
    currency_to.appendChild(createCurrencyOption("EUR"));
    currency_to.appendChild(createCurrencyOption("RUB"));
    form.appendChild(currency_to);
    var amount_label = document.createElement("label");
    amount_label.appendChild(document.createTextNode(" amount "));
    form.appendChild(amount_label);
    var amount = document.createElement("input");
    amount.setAttribute("id", "amount");
    amount.setAttribute("type", "text");
    form.appendChild(amount);
    var result = document.createElement("input");
    result.setAttribute("id", "result");
    result.setAttribute("type", "text");
    result.setAttribute("disabled", "disabled");
    form.appendChild(result);
    var button = document.createElement("input");
    button.setAttribute("id", "button");
    button.setAttribute("type", "button");
    button.setAttribute("value", "convert");
    button.setAttribute("onclick", "convert();");
    form.appendChild(button);
    document.documentElement.appendChild(form);
 })();