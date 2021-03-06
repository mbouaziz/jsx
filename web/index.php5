
<?
error_reporting(-1);
  require_once 'config.php5';
  require_once 'utilities.php5';
  require_once 'lang_options.php5';
  require_once 'env_options.php5';
  require_once 'bool_options.php5';
  
  $jsx_version = 'JSX (' . date(DATE_COOKIE, filemtime(jsx_bin)) . ')';
?>
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="en">
 <head>
  <meta http-equiv="Content-Language" content="en" />
  <meta http-equiv="Content-Type" content="text/html; charset=UTF-8" />
  <title>JSX Web</title>
  <script type="text/javascript" src="jquery-1.4.4.min.js"></script>
  <script type="text/javascript">
<?
  echo var_to_js('lang_tr', $lang_tr);
  echo var_to_js('envlist', $envlist);
?>
  </script>
  <script type="text/javascript" src="jsxweb.js"></script>
 </head>
 <body>
<div>
<form id="main_form" action="">
<table>
 <tr>
  <td>
   <table>
    <tr><td><?= $jsx_version ?></td>
     <td align="right">
<input type="button" id="doc" value="Documentation" />
<select id="sel_file">
 <option value="" selected="selected">Sample files here</option>
<?
  function options_of_dir($dt, $_env)
  {
    if (isset($dt['of']['_env']))
    {
      list($_env) = file($dt['of']['_env']);
      $_env = trim($_env);
      if ($_env != '' && $_env[0] != '|')
        $_env = '|' . $_env;
    }
  
    list($beg, $end) = ($dt['n'] != '' && !empty($dt['f'])) ? array('<optgroup label="' . $dt['n'] . '">' . "\n", '</optgroup>' . "\n") : array('', '');
    
    echo $beg;
    
    foreach ($dt['f'] as $f => $loc)
      echo ' <option value="', $loc, $_env, '">', $f, '</option>', "\n";

    echo $end;

    foreach ($dt['d'] as $d)
      options_of_dir($d, $_env);
  }

  options_of_dir(dir_tree('', samples_dir . '/', $lang_tr), '');
?>
</select>
<input type="button" id="load_sample" value="Load" />
     </td>
    </tr>
    <tr><td colspan="2">
<textarea name="jsx_src" id="jsx_src" cols="80" rows="24"></textarea>
    </td></tr>
   </table>
  </td>
  <td>
   <table>
<?
$checked = 'checked="checked" ';
foreach ($langlist as $lang => $desc)
{
  $id = 'jsx_lang_' . $lang;
	echo '<tr><td><input type="radio" name="jsx_lang" id="', $id, '" value="', $lang, '" ', $checked, '/></td>',
	     '<td><label for="', $id, '">', $desc, '</label></td></tr>', "\n";
	$checked = '';
}

echo '<tr><td colspan="2"><hr /></td></tr>';

foreach ($envlist as $filename => $infos)
{
	list($type, $default_checked) = $infos;
	$name = "jsx_env[$filename]";
	$id = 'jsx_env_' . $filename;
	$checked = $default_checked ? 'checked="checked" ' : '';
	echo '<tr><td><input type="checkbox" name="', $name, '" id="', $id, '" value="1" ', $checked, '/></td>',
	     '<td><a href="', $filename, '">', $filename, '</a> [', $type, ']</td></tr>', "\n";
}

echo '<tr><td colspan="2"><hr /></td></tr>';

foreach ($boolspeclist as $opt => $opt_a)
{
	list($default_checked, $desc) = $opt_a;
	$name = "jsx_opt[$opt]";
	$id = 'jsx_opt_' . $opt;
	$checked = $default_checked ? 'checked="checked" ' : '';
	echo '<tr><td><input type="checkbox" name="', $name, '" id="', $id, '" value="1" ', $checked, '/></td>',
	     '<td><label for="', $id, '">', $desc, '</label></td></tr>', "\n";
}
?>
    <tr><td colspan="2"><hr /></td></tr>
   </table>
  </td>
 </tr>
 <tr>
  <td><div id="status" /></td>
  <td><input type="submit" /></td>
 </tr>
</table>
</form>
</div>
<div id="result" />
 </body>
</html>
