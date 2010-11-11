<?
error_reporting(-1);
  require_once 'lang_options.php5';
  require_once 'env_options.php5';
  require_once 'bool_options.php5';
  require_once 'jsx.php5';

  function request_string($id)
  {
    return isset($_REQUEST[$id]) ? stripslashes($_REQUEST[$id]) : '';
  }

  function request_bool($id, $def = false)
  {
    return isset($_REQUEST[$id]) ? (bool)$_REQUEST[$id] : $def;
  }

  function request_var_in_array($id, $arr, $def)
  {
    if (!isset($_REQUEST[$id]))
      return $def;
    $v = $_REQUEST[$id];
    if (isset($arr[$v]))
      return $v;
    return $def;
  }
  
  function request_bool_array($id, $arr)
  {
    $r = array();
    foreach ($arr as $k => $v)
      $r[$k] = isset($_REQUEST[$id][$k]) ? (bool)$_REQUEST[$id][$k] : false;
    return $r;
  }

  $jsx_src = request_string('jsx_src');
  $jsx_do = request_bool('jsx_do');
  $firstlang = each($langlist);
  $jsx_lang = request_var_in_array('jsx_lang', $langlist, $firstlang[0]);
  $jsx_env = request_bool_array('jsx_env', $envlist);
  $jsx_opt = request_bool_array('jsx_opt', $boolspeclist);
?>
<html>
 <head>
  <title>Jsx Web</title>
 </head>
 <body>
<div>
<form action="<?= $PHP_SELF ?>" method="POST">
<input type="hidden" name="jsx_do" value="1" />
<table>
 <tr>
  <td>
<textarea name="jsx_src" cols="80" rows="20"><?= $jsx_src ?></textarea>
  </td>
  <td>
   <table>
<?
$id = 'jsx_lang';
foreach ($langlist as $lang => $desc)
{
  $checked = $jsx_lang == $lang ? 'checked="checked" ' : '';
	echo '<tr><td><input type="radio" name="', $id, '" id="', $id, '" value="', $lang, '" ', $checked, '/></td>',
	     '<td><label for="', $id, '">', $desc, '</label></td></tr>';
}

echo '<tr><td colspan="2"><hr /></td></tr>';

foreach ($envlist as $filename => $default_checked)
{
	$id = "jsx_env[$filename]";
	$checked = ($jsx_do && $jsx_env[$filename]) || (!$jsx_do && $default_checked) ? 'checked="checked" ' : '';
	echo '<tr><td><input type="checkbox" name="', $id, '" id="', $id, '" value="1" ', $checked, '/></td>',
	     '<td><label for="', $id, '"><a href="', $filename, '">', $filename, '</a></label></td></tr>';
}

echo '<tr><td colspan="2"><hr /></td></tr>';

foreach ($boolspeclist as $opt => $opt_a)
{
	list($default_checked, $desc) = $opt_a;
	$id = "jsx_opt[$opt]";
	$checked = ($jsx_do && $jsx_opt[$opt]) || (!$jsx_do && $default_checked) ? 'checked="checked" ' : '';
	echo '<tr><td><input type="checkbox" name="', $id, '" id="', $id, '" value="1" ', $checked, '/></td>',
	     '<td><label for="', $id, '">', $desc, '</label></td></tr>';
}
?>
    <tr><td colspan="2"><hr /></td></tr>
    <tr>
     <td>&nbsp;</td>
     <td><input type="submit" /></td>
    </tr>
   </table>
  </td>
 </tr>
 <tr>
</table>
</form>
</div>
<div>
<?
  if ($jsx_do)
  {
    echo jsx($jsx_src, $jsx_lang, $jsx_env, $jsx_opt);
  }
?>
</div>
 </body>
</html>
