
jQuery.fn.select_value = function (v)
{
  return this.each(function ()
  {
    for (var i = 0 ; i < this.length ; i++)
      if (this[i].value == v)
        return this[i].selected = "selected";
  });
}

var loaded_files = new Array();

var main_form_submit = function (event)
{
  event.preventDefault();

  $("#status").html("Sending source...");
  $("#result").fadeOut(400);
  
  var data = $(this).serializeArray();
  var onSuccess = function (res)
  {
    $("#status").hide().html("Executed!").fadeIn(400);
    $("#result").hide().html(res).fadeIn(400);
    $("#status").delay(2500).fadeOut(1500);
  };
  
  $.post("req.php5", data, onSuccess, "html");
};

var show_file = function (f)
{
  $("#status").html('File "' + f + '" loaded').show().delay(2500).fadeOut(1500);
  $("#jsx_src").val(loaded_files[f]);
  var ext = lang_tr[f.substr(f.lastIndexOf('.') + 1)];
  $('#jsx_lang_' + ext).click();
};

var load_sample = function ()
{
  var f = $("#sel_file").val();
  
  if (f == "")
    return;

  if (loaded_files[f] === undefined)
  {
    $("#status").html('Loading file "' + f + '"').show();
  
    $.get("samples/" + f, {}, function (content) { loaded_files[f] = content; show_file(f); }, "text");
  }
  else
    show_file(f);
};

var load_doc = function ()
{
  $("#sel_file").select_value("Documentation.js").change();
}

$(document).ready(function()
{
  $("#main_form").submit(main_form_submit);
  $("#sel_file").change(load_sample);
  $("#load_sample").click(load_sample);
  $("#doc").click(load_doc);
});

