<?
error_reporting(-1);
  require_once 'config.php5';
  require_once 'utilities.php5';
  require_once 'lang_options.php5';
  require_once 'env_options.php5';
  require_once 'bool_options.php5';
  
  $jsx_version = 'JSX (' . date(DATE_COOKIE, filemtime(jsx_bin)) . ')';
?>
<html>
 <head>
  <title>JSX Web</title>
  <script type="text/javascript" src="jquery-1.4.4.min.js"></script>
  <script type="text/javascript">
<?
  echo php_to_js_array('lang_tr', $lang_tr);
?>
  </script>
  <script type="text/javascript" src="jsxweb.js"></script>
 </head>
 <body>
<div>
<form id="main_form">
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
  function options_of_dir($dt)
  {
    list($beg, $end) = ($dt['n'] != '' && !empty($dt['f'])) ? array('<optgroup label="' . $dt['n'] . '">', '</optgroup>') : array('', '');
    
    echo $beg;
    
    foreach ($dt['f'] as $f => $loc)
      echo '<option value="', $loc, '">', $f, '</option>', "\n";
      
    foreach ($dt['d'] as $d)
      options_of_dir($d);
    
    echo $end;
  }

  options_of_dir(dir_tree('', samples_dir . '/', $lang_tr));
?>
</select>
<input type="button" id="load_sample" value="Load" />
     </td>
    </tr>
    <tr><td colspan="2">
<textarea name="jsx_src" id="jsx_src" cols="80" rows="20"></textarea>
    </td></tr>
   </table>
  </td>
  <td>
   <table>
<?
$id = 'jsx_lang';
$checked = 'checked="checked" ';
foreach ($langlist as $lang => $desc)
{
	echo '<tr><td><input type="radio" name="', $id, '" id="', $id, '" value="', $lang, '" ', $checked, '/></td>',
	     '<td><label for="', $id, '">', $desc, '</label></td></tr>';
	$checked = '';
}

echo '<tr><td colspan="2"><hr /></td></tr>';

foreach ($envlist as $filename => $default_checked)
{
	$id = "jsx_env[$filename]";
	$checked = $default_checked ? 'checked="checked" ' : '';
	echo '<tr><td><input type="checkbox" name="', $id, '" id="', $id, '" value="1" ', $checked, '/></td>',
	     '<td><a href="', $filename, '">', $filename, '</a></td></tr>';
}

echo '<tr><td colspan="2"><hr /></td></tr>';

foreach ($boolspeclist as $opt => $opt_a)
{
	list($default_checked, $desc) = $opt_a;
	$id = "jsx_opt[$opt]";
	$checked = $default_checked ? 'checked="checked" ' : '';
	echo '<tr><td><input type="checkbox" name="', $id, '" id="', $id, '" value="1" ', $checked, '/></td>',
	     '<td><label for="', $id, '">', $desc, '</label></td></tr>';
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
